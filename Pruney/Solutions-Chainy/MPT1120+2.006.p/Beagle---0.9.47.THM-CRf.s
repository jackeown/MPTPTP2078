%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:03 EST 2020

% Result     : Theorem 9.32s
% Output     : CNFRefutation 9.61s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 184 expanded)
%              Number of leaves         :   28 (  74 expanded)
%              Depth                    :   13
%              Number of atoms          :   98 ( 283 expanded)
%              Number of equality atoms :   18 (  78 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)),k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_pre_topc)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_49,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_59,axiom,(
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

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_65,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | ~ m1_subset_1(A_37,k1_zfmisc_1(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_73,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_65])).

tff(c_10,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_109,plain,(
    ! [A_45,B_46] : k1_setfam_1(k2_tarski(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_134,plain,(
    ! [B_50,A_51] : k1_setfam_1(k2_tarski(B_50,A_51)) = k3_xboole_0(A_51,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_109])).

tff(c_14,plain,(
    ! [A_16,B_17] : k1_setfam_1(k2_tarski(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_140,plain,(
    ! [B_50,A_51] : k3_xboole_0(B_50,A_51) = k3_xboole_0(A_51,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_14])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_74,plain,(
    ! [A_39,B_40] :
      ( k2_xboole_0(A_39,B_40) = B_40
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_86,plain,(
    ! [A_6,B_7] : k2_xboole_0(k3_xboole_0(A_6,B_7),A_6) = A_6 ),
    inference(resolution,[status(thm)],[c_6,c_74])).

tff(c_124,plain,(
    ! [A_47,C_48,B_49] :
      ( r1_tarski(A_47,C_48)
      | ~ r1_tarski(k2_xboole_0(A_47,B_49),C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_277,plain,(
    ! [A_63,B_64,C_65] :
      ( r1_tarski(k3_xboole_0(A_63,B_64),C_65)
      | ~ r1_tarski(A_63,C_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_124])).

tff(c_283,plain,(
    ! [B_50,A_51,C_65] :
      ( r1_tarski(k3_xboole_0(B_50,A_51),C_65)
      | ~ r1_tarski(A_51,C_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_277])).

tff(c_18,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_157,plain,(
    ! [B_52,A_53] : k3_xboole_0(B_52,A_53) = k3_xboole_0(A_53,B_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_14])).

tff(c_178,plain,(
    ! [B_52,A_53] : r1_tarski(k3_xboole_0(B_52,A_53),A_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_6])).

tff(c_22,plain,(
    ! [A_22,B_26,C_28] :
      ( r1_tarski(k2_pre_topc(A_22,B_26),k2_pre_topc(A_22,C_28))
      | ~ r1_tarski(B_26,C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] :
      ( r1_tarski(A_8,k3_xboole_0(B_9,C_10))
      | ~ r1_tarski(A_8,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_481,plain,(
    ! [A_91,B_92] :
      ( m1_subset_1(k2_pre_topc(A_91,B_92),k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    ! [A_13,B_14,C_15] :
      ( k9_subset_1(A_13,B_14,C_15) = k3_xboole_0(B_14,C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2713,plain,(
    ! [A_175,B_176,B_177] :
      ( k9_subset_1(u1_struct_0(A_175),B_176,k2_pre_topc(A_175,B_177)) = k3_xboole_0(B_176,k2_pre_topc(A_175,B_177))
      | ~ m1_subset_1(B_177,k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ l1_pre_topc(A_175) ) ),
    inference(resolution,[status(thm)],[c_481,c_12])).

tff(c_2720,plain,(
    ! [B_176] :
      ( k9_subset_1(u1_struct_0('#skF_1'),B_176,k2_pre_topc('#skF_1','#skF_3')) = k3_xboole_0(B_176,k2_pre_topc('#skF_1','#skF_3'))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_2713])).

tff(c_2727,plain,(
    ! [B_176] : k9_subset_1(u1_struct_0('#skF_1'),B_176,k2_pre_topc('#skF_1','#skF_3')) = k3_xboole_0(B_176,k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2720])).

tff(c_384,plain,(
    ! [A_77,B_78,C_79] :
      ( k9_subset_1(A_77,B_78,C_79) = k3_xboole_0(B_78,C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_392,plain,(
    ! [B_78] : k9_subset_1(u1_struct_0('#skF_1'),B_78,'#skF_3') = k3_xboole_0(B_78,'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_384])).

tff(c_24,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_394,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_24])).

tff(c_395,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_394])).

tff(c_2734,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2727,c_395])).

tff(c_2735,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_2734])).

tff(c_3023,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k2_pre_topc('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_2735])).

tff(c_11680,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k2_pre_topc('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3023])).

tff(c_11683,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_11680])).

tff(c_11686,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_6,c_11683])).

tff(c_11690,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_18,c_11686])).

tff(c_11705,plain,(
    ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_283,c_11690])).

tff(c_11716,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_11705])).

tff(c_11717,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_3023])).

tff(c_11799,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_11717])).

tff(c_11802,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_178,c_11799])).

tff(c_11806,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_18,c_11802])).

tff(c_11821,plain,(
    ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_283,c_11806])).

tff(c_11832,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_11821])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:04:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.32/3.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.32/3.45  
% 9.32/3.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.32/3.45  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 9.32/3.45  
% 9.32/3.45  %Foreground sorts:
% 9.32/3.45  
% 9.32/3.45  
% 9.32/3.45  %Background operators:
% 9.32/3.45  
% 9.32/3.45  
% 9.32/3.45  %Foreground operators:
% 9.32/3.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.32/3.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.32/3.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.32/3.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.32/3.45  tff('#skF_2', type, '#skF_2': $i).
% 9.32/3.45  tff('#skF_3', type, '#skF_3': $i).
% 9.32/3.45  tff('#skF_1', type, '#skF_1': $i).
% 9.32/3.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.32/3.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.32/3.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.32/3.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.32/3.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.32/3.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.32/3.45  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 9.32/3.45  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 9.32/3.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.32/3.45  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.32/3.45  
% 9.61/3.47  tff(f_82, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)), k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_pre_topc)).
% 9.61/3.47  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.61/3.47  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 9.61/3.47  tff(f_49, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 9.61/3.47  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 9.61/3.47  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 9.61/3.47  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 9.61/3.47  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_pre_topc)).
% 9.61/3.47  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 9.61/3.47  tff(f_59, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 9.61/3.47  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 9.61/3.47  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.61/3.47  tff(c_65, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | ~m1_subset_1(A_37, k1_zfmisc_1(B_38)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.61/3.47  tff(c_73, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_65])).
% 9.61/3.47  tff(c_10, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.61/3.47  tff(c_109, plain, (![A_45, B_46]: (k1_setfam_1(k2_tarski(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.61/3.47  tff(c_134, plain, (![B_50, A_51]: (k1_setfam_1(k2_tarski(B_50, A_51))=k3_xboole_0(A_51, B_50))), inference(superposition, [status(thm), theory('equality')], [c_10, c_109])).
% 9.61/3.47  tff(c_14, plain, (![A_16, B_17]: (k1_setfam_1(k2_tarski(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.61/3.47  tff(c_140, plain, (![B_50, A_51]: (k3_xboole_0(B_50, A_51)=k3_xboole_0(A_51, B_50))), inference(superposition, [status(thm), theory('equality')], [c_134, c_14])).
% 9.61/3.47  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.61/3.47  tff(c_74, plain, (![A_39, B_40]: (k2_xboole_0(A_39, B_40)=B_40 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.61/3.47  tff(c_86, plain, (![A_6, B_7]: (k2_xboole_0(k3_xboole_0(A_6, B_7), A_6)=A_6)), inference(resolution, [status(thm)], [c_6, c_74])).
% 9.61/3.47  tff(c_124, plain, (![A_47, C_48, B_49]: (r1_tarski(A_47, C_48) | ~r1_tarski(k2_xboole_0(A_47, B_49), C_48))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.61/3.47  tff(c_277, plain, (![A_63, B_64, C_65]: (r1_tarski(k3_xboole_0(A_63, B_64), C_65) | ~r1_tarski(A_63, C_65))), inference(superposition, [status(thm), theory('equality')], [c_86, c_124])).
% 9.61/3.47  tff(c_283, plain, (![B_50, A_51, C_65]: (r1_tarski(k3_xboole_0(B_50, A_51), C_65) | ~r1_tarski(A_51, C_65))), inference(superposition, [status(thm), theory('equality')], [c_140, c_277])).
% 9.61/3.47  tff(c_18, plain, (![A_18, B_19]: (m1_subset_1(A_18, k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.61/3.47  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.61/3.47  tff(c_157, plain, (![B_52, A_53]: (k3_xboole_0(B_52, A_53)=k3_xboole_0(A_53, B_52))), inference(superposition, [status(thm), theory('equality')], [c_134, c_14])).
% 9.61/3.47  tff(c_178, plain, (![B_52, A_53]: (r1_tarski(k3_xboole_0(B_52, A_53), A_53))), inference(superposition, [status(thm), theory('equality')], [c_157, c_6])).
% 9.61/3.47  tff(c_22, plain, (![A_22, B_26, C_28]: (r1_tarski(k2_pre_topc(A_22, B_26), k2_pre_topc(A_22, C_28)) | ~r1_tarski(B_26, C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(u1_struct_0(A_22))) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.61/3.47  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.61/3.47  tff(c_8, plain, (![A_8, B_9, C_10]: (r1_tarski(A_8, k3_xboole_0(B_9, C_10)) | ~r1_tarski(A_8, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.61/3.47  tff(c_481, plain, (![A_91, B_92]: (m1_subset_1(k2_pre_topc(A_91, B_92), k1_zfmisc_1(u1_struct_0(A_91))) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.61/3.47  tff(c_12, plain, (![A_13, B_14, C_15]: (k9_subset_1(A_13, B_14, C_15)=k3_xboole_0(B_14, C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.61/3.47  tff(c_2713, plain, (![A_175, B_176, B_177]: (k9_subset_1(u1_struct_0(A_175), B_176, k2_pre_topc(A_175, B_177))=k3_xboole_0(B_176, k2_pre_topc(A_175, B_177)) | ~m1_subset_1(B_177, k1_zfmisc_1(u1_struct_0(A_175))) | ~l1_pre_topc(A_175))), inference(resolution, [status(thm)], [c_481, c_12])).
% 9.61/3.47  tff(c_2720, plain, (![B_176]: (k9_subset_1(u1_struct_0('#skF_1'), B_176, k2_pre_topc('#skF_1', '#skF_3'))=k3_xboole_0(B_176, k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_2713])).
% 9.61/3.47  tff(c_2727, plain, (![B_176]: (k9_subset_1(u1_struct_0('#skF_1'), B_176, k2_pre_topc('#skF_1', '#skF_3'))=k3_xboole_0(B_176, k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2720])).
% 9.61/3.47  tff(c_384, plain, (![A_77, B_78, C_79]: (k9_subset_1(A_77, B_78, C_79)=k3_xboole_0(B_78, C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.61/3.47  tff(c_392, plain, (![B_78]: (k9_subset_1(u1_struct_0('#skF_1'), B_78, '#skF_3')=k3_xboole_0(B_78, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_384])).
% 9.61/3.47  tff(c_24, plain, (~r1_tarski(k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.61/3.47  tff(c_394, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_392, c_24])).
% 9.61/3.47  tff(c_395, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_394])).
% 9.61/3.47  tff(c_2734, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2727, c_395])).
% 9.61/3.47  tff(c_2735, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_2734])).
% 9.61/3.47  tff(c_3023, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k2_pre_topc('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_8, c_2735])).
% 9.61/3.47  tff(c_11680, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k2_pre_topc('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_3023])).
% 9.61/3.47  tff(c_11683, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_11680])).
% 9.61/3.47  tff(c_11686, plain, (~m1_subset_1(k3_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_6, c_11683])).
% 9.61/3.47  tff(c_11690, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_11686])).
% 9.61/3.47  tff(c_11705, plain, (~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_283, c_11690])).
% 9.61/3.47  tff(c_11716, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_11705])).
% 9.61/3.47  tff(c_11717, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_3023])).
% 9.61/3.47  tff(c_11799, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_11717])).
% 9.61/3.47  tff(c_11802, plain, (~m1_subset_1(k3_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_178, c_11799])).
% 9.61/3.47  tff(c_11806, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_11802])).
% 9.61/3.47  tff(c_11821, plain, (~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_283, c_11806])).
% 9.61/3.47  tff(c_11832, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_11821])).
% 9.61/3.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.61/3.47  
% 9.61/3.47  Inference rules
% 9.61/3.47  ----------------------
% 9.61/3.47  #Ref     : 0
% 9.61/3.47  #Sup     : 3046
% 9.61/3.47  #Fact    : 0
% 9.61/3.47  #Define  : 0
% 9.61/3.47  #Split   : 5
% 9.61/3.47  #Chain   : 0
% 9.61/3.47  #Close   : 0
% 9.61/3.47  
% 9.61/3.47  Ordering : KBO
% 9.61/3.47  
% 9.61/3.47  Simplification rules
% 9.61/3.47  ----------------------
% 9.61/3.47  #Subsume      : 294
% 9.61/3.47  #Demod        : 919
% 9.61/3.47  #Tautology    : 1212
% 9.61/3.47  #SimpNegUnit  : 0
% 9.61/3.47  #BackRed      : 2
% 9.61/3.47  
% 9.61/3.47  #Partial instantiations: 0
% 9.61/3.47  #Strategies tried      : 1
% 9.61/3.47  
% 9.61/3.47  Timing (in seconds)
% 9.61/3.47  ----------------------
% 9.61/3.47  Preprocessing        : 0.29
% 9.61/3.47  Parsing              : 0.16
% 9.61/3.47  CNF conversion       : 0.02
% 9.61/3.47  Main loop            : 2.40
% 9.61/3.47  Inferencing          : 0.49
% 9.61/3.47  Reduction            : 1.26
% 9.61/3.47  Demodulation         : 1.13
% 9.61/3.47  BG Simplification    : 0.06
% 9.61/3.47  Subsumption          : 0.45
% 9.61/3.47  Abstraction          : 0.08
% 9.61/3.47  MUC search           : 0.00
% 9.61/3.47  Cooper               : 0.00
% 9.61/3.47  Total                : 2.73
% 9.61/3.47  Index Insertion      : 0.00
% 9.61/3.47  Index Deletion       : 0.00
% 9.61/3.47  Index Matching       : 0.00
% 9.61/3.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------

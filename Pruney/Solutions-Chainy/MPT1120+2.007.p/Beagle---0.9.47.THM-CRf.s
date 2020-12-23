%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:03 EST 2020

% Result     : Theorem 10.74s
% Output     : CNFRefutation 10.74s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 207 expanded)
%              Number of leaves         :   26 (  81 expanded)
%              Depth                    :   13
%              Number of atoms          :  113 ( 349 expanded)
%              Number of equality atoms :   15 (  72 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)),k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_pre_topc)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

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

tff(c_8,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_72,plain,(
    ! [A_37,B_38] : k1_setfam_1(k2_tarski(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_92,plain,(
    ! [B_41,A_42] : k1_setfam_1(k2_tarski(B_41,A_42)) = k3_xboole_0(A_42,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_72])).

tff(c_12,plain,(
    ! [A_14,B_15] : k1_setfam_1(k2_tarski(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_98,plain,(
    ! [B_41,A_42] : k3_xboole_0(B_41,A_42) = k3_xboole_0(A_42,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_12])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_378,plain,(
    ! [A_75,B_76,C_77] :
      ( r1_tarski(A_75,k3_xboole_0(B_76,C_77))
      | ~ r1_tarski(A_75,C_77)
      | ~ r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(B_7,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1090,plain,(
    ! [A_136,B_137,C_138,A_139] :
      ( r1_tarski(A_136,k3_xboole_0(B_137,C_138))
      | ~ r1_tarski(A_136,A_139)
      | ~ r1_tarski(A_139,C_138)
      | ~ r1_tarski(A_139,B_137) ) ),
    inference(resolution,[status(thm)],[c_378,c_6])).

tff(c_3901,plain,(
    ! [A_223,B_224,B_225,C_226] :
      ( r1_tarski(k3_xboole_0(A_223,B_224),k3_xboole_0(B_225,C_226))
      | ~ r1_tarski(A_223,C_226)
      | ~ r1_tarski(A_223,B_225) ) ),
    inference(resolution,[status(thm)],[c_2,c_1090])).

tff(c_164,plain,(
    ! [A_47,C_48,B_49] :
      ( r1_tarski(A_47,C_48)
      | ~ r1_tarski(B_49,C_48)
      | ~ r1_tarski(A_47,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_176,plain,(
    ! [A_47,A_1,B_2] :
      ( r1_tarski(A_47,A_1)
      | ~ r1_tarski(A_47,k3_xboole_0(A_1,B_2)) ) ),
    inference(resolution,[status(thm)],[c_2,c_164])).

tff(c_4812,plain,(
    ! [A_230,B_231,B_232,C_233] :
      ( r1_tarski(k3_xboole_0(A_230,B_231),B_232)
      | ~ r1_tarski(A_230,C_233)
      | ~ r1_tarski(A_230,B_232) ) ),
    inference(resolution,[status(thm)],[c_3901,c_176])).

tff(c_4997,plain,(
    ! [B_238,B_239] :
      ( r1_tarski(k3_xboole_0('#skF_2',B_238),B_239)
      | ~ r1_tarski('#skF_2',B_239) ) ),
    inference(resolution,[status(thm)],[c_71,c_4812])).

tff(c_5048,plain,(
    ! [B_41,B_239] :
      ( r1_tarski(k3_xboole_0(B_41,'#skF_2'),B_239)
      | ~ r1_tarski('#skF_2',B_239) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_4997])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_115,plain,(
    ! [B_43,A_44] : k3_xboole_0(B_43,A_44) = k3_xboole_0(A_44,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_12])).

tff(c_130,plain,(
    ! [B_43,A_44] : r1_tarski(k3_xboole_0(B_43,A_44),A_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_2])).

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

tff(c_548,plain,(
    ! [A_94,B_95] :
      ( m1_subset_1(k2_pre_topc(A_94,B_95),k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13] :
      ( k9_subset_1(A_11,B_12,C_13) = k3_xboole_0(B_12,C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1457,plain,(
    ! [A_154,B_155,B_156] :
      ( k9_subset_1(u1_struct_0(A_154),B_155,k2_pre_topc(A_154,B_156)) = k3_xboole_0(B_155,k2_pre_topc(A_154,B_156))
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_pre_topc(A_154) ) ),
    inference(resolution,[status(thm)],[c_548,c_10])).

tff(c_1464,plain,(
    ! [B_155] :
      ( k9_subset_1(u1_struct_0('#skF_1'),B_155,k2_pre_topc('#skF_1','#skF_3')) = k3_xboole_0(B_155,k2_pre_topc('#skF_1','#skF_3'))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_1457])).

tff(c_1471,plain,(
    ! [B_155] : k9_subset_1(u1_struct_0('#skF_1'),B_155,k2_pre_topc('#skF_1','#skF_3')) = k3_xboole_0(B_155,k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1464])).

tff(c_277,plain,(
    ! [A_64,B_65,C_66] :
      ( k9_subset_1(A_64,B_65,C_66) = k3_xboole_0(B_65,C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_285,plain,(
    ! [B_65] : k9_subset_1(u1_struct_0('#skF_1'),B_65,'#skF_3') = k3_xboole_0(B_65,'#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_277])).

tff(c_22,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_328,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_22])).

tff(c_329,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_328])).

tff(c_1567,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1471,c_329])).

tff(c_1568,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_1567])).

tff(c_3136,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k2_pre_topc('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_1568])).

tff(c_11924,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k2_pre_topc('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3136])).

tff(c_11969,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_11924])).

tff(c_11972,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_2,c_11969])).

tff(c_11976,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_16,c_11972])).

tff(c_11979,plain,(
    ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_5048,c_11976])).

tff(c_12004,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_11979])).

tff(c_12005,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_3136])).

tff(c_12051,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_12005])).

tff(c_12054,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_130,c_12051])).

tff(c_12058,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_16,c_12054])).

tff(c_12061,plain,(
    ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_5048,c_12058])).

tff(c_12086,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_12061])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:44:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.74/3.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.74/3.50  
% 10.74/3.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.74/3.51  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 10.74/3.51  
% 10.74/3.51  %Foreground sorts:
% 10.74/3.51  
% 10.74/3.51  
% 10.74/3.51  %Background operators:
% 10.74/3.51  
% 10.74/3.51  
% 10.74/3.51  %Foreground operators:
% 10.74/3.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.74/3.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.74/3.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.74/3.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.74/3.51  tff('#skF_2', type, '#skF_2': $i).
% 10.74/3.51  tff('#skF_3', type, '#skF_3': $i).
% 10.74/3.51  tff('#skF_1', type, '#skF_1': $i).
% 10.74/3.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.74/3.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.74/3.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.74/3.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.74/3.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.74/3.51  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 10.74/3.51  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 10.74/3.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.74/3.51  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.74/3.51  
% 10.74/3.52  tff(f_80, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)), k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_pre_topc)).
% 10.74/3.52  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.74/3.52  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 10.74/3.52  tff(f_47, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 10.74/3.52  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 10.74/3.52  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 10.74/3.52  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 10.74/3.52  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_pre_topc)).
% 10.74/3.52  tff(f_57, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 10.74/3.52  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 10.74/3.52  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.74/3.52  tff(c_63, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | ~m1_subset_1(A_35, k1_zfmisc_1(B_36)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.74/3.52  tff(c_71, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_63])).
% 10.74/3.52  tff(c_8, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.74/3.52  tff(c_72, plain, (![A_37, B_38]: (k1_setfam_1(k2_tarski(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.74/3.52  tff(c_92, plain, (![B_41, A_42]: (k1_setfam_1(k2_tarski(B_41, A_42))=k3_xboole_0(A_42, B_41))), inference(superposition, [status(thm), theory('equality')], [c_8, c_72])).
% 10.74/3.52  tff(c_12, plain, (![A_14, B_15]: (k1_setfam_1(k2_tarski(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.74/3.52  tff(c_98, plain, (![B_41, A_42]: (k3_xboole_0(B_41, A_42)=k3_xboole_0(A_42, B_41))), inference(superposition, [status(thm), theory('equality')], [c_92, c_12])).
% 10.74/3.52  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.74/3.52  tff(c_378, plain, (![A_75, B_76, C_77]: (r1_tarski(A_75, k3_xboole_0(B_76, C_77)) | ~r1_tarski(A_75, C_77) | ~r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.74/3.52  tff(c_6, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(B_7, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.74/3.52  tff(c_1090, plain, (![A_136, B_137, C_138, A_139]: (r1_tarski(A_136, k3_xboole_0(B_137, C_138)) | ~r1_tarski(A_136, A_139) | ~r1_tarski(A_139, C_138) | ~r1_tarski(A_139, B_137))), inference(resolution, [status(thm)], [c_378, c_6])).
% 10.74/3.52  tff(c_3901, plain, (![A_223, B_224, B_225, C_226]: (r1_tarski(k3_xboole_0(A_223, B_224), k3_xboole_0(B_225, C_226)) | ~r1_tarski(A_223, C_226) | ~r1_tarski(A_223, B_225))), inference(resolution, [status(thm)], [c_2, c_1090])).
% 10.74/3.52  tff(c_164, plain, (![A_47, C_48, B_49]: (r1_tarski(A_47, C_48) | ~r1_tarski(B_49, C_48) | ~r1_tarski(A_47, B_49))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.74/3.52  tff(c_176, plain, (![A_47, A_1, B_2]: (r1_tarski(A_47, A_1) | ~r1_tarski(A_47, k3_xboole_0(A_1, B_2)))), inference(resolution, [status(thm)], [c_2, c_164])).
% 10.74/3.52  tff(c_4812, plain, (![A_230, B_231, B_232, C_233]: (r1_tarski(k3_xboole_0(A_230, B_231), B_232) | ~r1_tarski(A_230, C_233) | ~r1_tarski(A_230, B_232))), inference(resolution, [status(thm)], [c_3901, c_176])).
% 10.74/3.52  tff(c_4997, plain, (![B_238, B_239]: (r1_tarski(k3_xboole_0('#skF_2', B_238), B_239) | ~r1_tarski('#skF_2', B_239))), inference(resolution, [status(thm)], [c_71, c_4812])).
% 10.74/3.52  tff(c_5048, plain, (![B_41, B_239]: (r1_tarski(k3_xboole_0(B_41, '#skF_2'), B_239) | ~r1_tarski('#skF_2', B_239))), inference(superposition, [status(thm), theory('equality')], [c_98, c_4997])).
% 10.74/3.52  tff(c_16, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.74/3.52  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.74/3.52  tff(c_115, plain, (![B_43, A_44]: (k3_xboole_0(B_43, A_44)=k3_xboole_0(A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_92, c_12])).
% 10.74/3.52  tff(c_130, plain, (![B_43, A_44]: (r1_tarski(k3_xboole_0(B_43, A_44), A_44))), inference(superposition, [status(thm), theory('equality')], [c_115, c_2])).
% 10.74/3.52  tff(c_20, plain, (![A_20, B_24, C_26]: (r1_tarski(k2_pre_topc(A_20, B_24), k2_pre_topc(A_20, C_26)) | ~r1_tarski(B_24, C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(u1_struct_0(A_20))) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.74/3.52  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.74/3.52  tff(c_4, plain, (![A_3, B_4, C_5]: (r1_tarski(A_3, k3_xboole_0(B_4, C_5)) | ~r1_tarski(A_3, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.74/3.52  tff(c_548, plain, (![A_94, B_95]: (m1_subset_1(k2_pre_topc(A_94, B_95), k1_zfmisc_1(u1_struct_0(A_94))) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.74/3.52  tff(c_10, plain, (![A_11, B_12, C_13]: (k9_subset_1(A_11, B_12, C_13)=k3_xboole_0(B_12, C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.74/3.52  tff(c_1457, plain, (![A_154, B_155, B_156]: (k9_subset_1(u1_struct_0(A_154), B_155, k2_pre_topc(A_154, B_156))=k3_xboole_0(B_155, k2_pre_topc(A_154, B_156)) | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_pre_topc(A_154))), inference(resolution, [status(thm)], [c_548, c_10])).
% 10.74/3.52  tff(c_1464, plain, (![B_155]: (k9_subset_1(u1_struct_0('#skF_1'), B_155, k2_pre_topc('#skF_1', '#skF_3'))=k3_xboole_0(B_155, k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_1457])).
% 10.74/3.52  tff(c_1471, plain, (![B_155]: (k9_subset_1(u1_struct_0('#skF_1'), B_155, k2_pre_topc('#skF_1', '#skF_3'))=k3_xboole_0(B_155, k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1464])).
% 10.74/3.52  tff(c_277, plain, (![A_64, B_65, C_66]: (k9_subset_1(A_64, B_65, C_66)=k3_xboole_0(B_65, C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.74/3.52  tff(c_285, plain, (![B_65]: (k9_subset_1(u1_struct_0('#skF_1'), B_65, '#skF_3')=k3_xboole_0(B_65, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_277])).
% 10.74/3.52  tff(c_22, plain, (~r1_tarski(k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.74/3.52  tff(c_328, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_285, c_22])).
% 10.74/3.52  tff(c_329, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_328])).
% 10.74/3.52  tff(c_1567, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1471, c_329])).
% 10.74/3.52  tff(c_1568, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_1567])).
% 10.74/3.52  tff(c_3136, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k2_pre_topc('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_1568])).
% 10.74/3.52  tff(c_11924, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k2_pre_topc('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_3136])).
% 10.74/3.52  tff(c_11969, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_11924])).
% 10.74/3.52  tff(c_11972, plain, (~m1_subset_1(k3_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_2, c_11969])).
% 10.74/3.52  tff(c_11976, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_11972])).
% 10.74/3.52  tff(c_11979, plain, (~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_5048, c_11976])).
% 10.74/3.52  tff(c_12004, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_11979])).
% 10.74/3.52  tff(c_12005, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_3136])).
% 10.74/3.52  tff(c_12051, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_12005])).
% 10.74/3.52  tff(c_12054, plain, (~m1_subset_1(k3_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_130, c_12051])).
% 10.74/3.52  tff(c_12058, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_12054])).
% 10.74/3.52  tff(c_12061, plain, (~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_5048, c_12058])).
% 10.74/3.52  tff(c_12086, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_12061])).
% 10.74/3.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.74/3.52  
% 10.74/3.52  Inference rules
% 10.74/3.52  ----------------------
% 10.74/3.52  #Ref     : 0
% 10.74/3.52  #Sup     : 3173
% 10.74/3.52  #Fact    : 0
% 10.74/3.52  #Define  : 0
% 10.74/3.52  #Split   : 11
% 10.74/3.52  #Chain   : 0
% 10.74/3.52  #Close   : 0
% 10.74/3.52  
% 10.74/3.52  Ordering : KBO
% 10.74/3.52  
% 10.74/3.52  Simplification rules
% 10.74/3.52  ----------------------
% 10.74/3.52  #Subsume      : 887
% 10.74/3.52  #Demod        : 494
% 10.74/3.52  #Tautology    : 526
% 10.74/3.52  #SimpNegUnit  : 0
% 10.74/3.52  #BackRed      : 2
% 10.74/3.52  
% 10.74/3.52  #Partial instantiations: 0
% 10.74/3.52  #Strategies tried      : 1
% 10.74/3.52  
% 10.74/3.52  Timing (in seconds)
% 10.74/3.52  ----------------------
% 10.74/3.52  Preprocessing        : 0.32
% 10.74/3.53  Parsing              : 0.17
% 10.74/3.53  CNF conversion       : 0.02
% 10.74/3.53  Main loop            : 2.42
% 10.74/3.53  Inferencing          : 0.55
% 10.74/3.53  Reduction            : 1.09
% 10.74/3.53  Demodulation         : 0.95
% 10.74/3.53  BG Simplification    : 0.07
% 10.74/3.53  Subsumption          : 0.55
% 10.74/3.53  Abstraction          : 0.08
% 10.74/3.53  MUC search           : 0.00
% 10.74/3.53  Cooper               : 0.00
% 10.74/3.53  Total                : 2.77
% 10.74/3.53  Index Insertion      : 0.00
% 10.74/3.53  Index Deletion       : 0.00
% 10.74/3.53  Index Matching       : 0.00
% 10.74/3.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:03 EST 2020

% Result     : Theorem 3.66s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 171 expanded)
%              Number of leaves         :   26 (  69 expanded)
%              Depth                    :   13
%              Number of atoms          :   91 ( 265 expanded)
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

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)),k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_pre_topc)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_45,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_63,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,B_36)
      | ~ m1_subset_1(A_35,k1_zfmisc_1(B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_71,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_63])).

tff(c_8,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_72,plain,(
    ! [A_37,B_38] : k1_setfam_1(k2_tarski(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_92,plain,(
    ! [B_41,A_42] : k1_setfam_1(k2_tarski(B_41,A_42)) = k3_xboole_0(A_42,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_72])).

tff(c_12,plain,(
    ! [A_14,B_15] : k1_setfam_1(k2_tarski(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_98,plain,(
    ! [B_41,A_42] : k3_xboole_0(B_41,A_42) = k3_xboole_0(A_42,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_12])).

tff(c_164,plain,(
    ! [A_47,C_48,B_49] :
      ( r1_tarski(k3_xboole_0(A_47,C_48),B_49)
      | ~ r1_tarski(A_47,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_170,plain,(
    ! [A_42,B_41,B_49] :
      ( r1_tarski(k3_xboole_0(A_42,B_41),B_49)
      | ~ r1_tarski(B_41,B_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_164])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_115,plain,(
    ! [B_43,A_44] : k3_xboole_0(B_43,A_44) = k3_xboole_0(A_44,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_12])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(k3_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_130,plain,(
    ! [B_43,A_44] : r1_tarski(k3_xboole_0(B_43,A_44),A_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_4])).

tff(c_20,plain,(
    ! [A_20,B_24,C_26] :
      ( r1_tarski(k2_pre_topc(A_20,B_24),k2_pre_topc(A_20,C_26))
      | ~ r1_tarski(B_24,C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] :
      ( r1_tarski(A_6,k3_xboole_0(B_7,C_8))
      | ~ r1_tarski(A_6,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_240,plain,(
    ! [A_64,B_65] :
      ( m1_subset_1(k2_pre_topc(A_64,B_65),k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13] :
      ( k9_subset_1(A_11,B_12,C_13) = k3_xboole_0(B_12,C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1301,plain,(
    ! [A_106,B_107,B_108] :
      ( k9_subset_1(u1_struct_0(A_106),B_107,k2_pre_topc(A_106,B_108)) = k3_xboole_0(B_107,k2_pre_topc(A_106,B_108))
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(resolution,[status(thm)],[c_240,c_10])).

tff(c_1308,plain,(
    ! [B_107] :
      ( k9_subset_1(u1_struct_0('#skF_1'),B_107,k2_pre_topc('#skF_1','#skF_3')) = k3_xboole_0(B_107,k2_pre_topc('#skF_1','#skF_3'))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_1301])).

tff(c_1315,plain,(
    ! [B_107] : k9_subset_1(u1_struct_0('#skF_1'),B_107,k2_pre_topc('#skF_1','#skF_3')) = k3_xboole_0(B_107,k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1308])).

tff(c_179,plain,(
    ! [A_53,B_54,C_55] :
      ( k9_subset_1(A_53,B_54,C_55) = k3_xboole_0(B_54,C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_187,plain,(
    ! [B_54] : k9_subset_1(u1_struct_0('#skF_1'),B_54,'#skF_3') = k3_xboole_0(B_54,'#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_179])).

tff(c_22,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_189,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_22])).

tff(c_190,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_189])).

tff(c_1319,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1315,c_190])).

tff(c_1320,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_1319])).

tff(c_1342,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k2_pre_topc('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_1320])).

tff(c_1721,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k2_pre_topc('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1342])).

tff(c_1724,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_1721])).

tff(c_1727,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_4,c_1724])).

tff(c_1731,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_16,c_1727])).

tff(c_1734,plain,(
    ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_170,c_1731])).

tff(c_1741,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_1734])).

tff(c_1742,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1342])).

tff(c_1746,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_1742])).

tff(c_1749,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_130,c_1746])).

tff(c_1753,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_16,c_1749])).

tff(c_1835,plain,(
    ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_170,c_1753])).

tff(c_1842,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_1835])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:18:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.66/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.64  
% 3.66/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.64  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 3.66/1.64  
% 3.66/1.64  %Foreground sorts:
% 3.66/1.64  
% 3.66/1.64  
% 3.66/1.64  %Background operators:
% 3.66/1.64  
% 3.66/1.64  
% 3.66/1.64  %Foreground operators:
% 3.66/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.66/1.64  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.66/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.66/1.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.66/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.66/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.66/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.66/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.66/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.66/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.66/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.66/1.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.66/1.64  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.66/1.64  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.66/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.66/1.64  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.66/1.64  
% 3.98/1.66  tff(f_78, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)), k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_pre_topc)).
% 3.98/1.66  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.98/1.66  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.98/1.66  tff(f_45, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.98/1.66  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 3.98/1.66  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.98/1.66  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_pre_topc)).
% 3.98/1.66  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.98/1.66  tff(f_55, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 3.98/1.66  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.98/1.66  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.98/1.66  tff(c_63, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | ~m1_subset_1(A_35, k1_zfmisc_1(B_36)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.98/1.66  tff(c_71, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_63])).
% 3.98/1.66  tff(c_8, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.98/1.66  tff(c_72, plain, (![A_37, B_38]: (k1_setfam_1(k2_tarski(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.98/1.66  tff(c_92, plain, (![B_41, A_42]: (k1_setfam_1(k2_tarski(B_41, A_42))=k3_xboole_0(A_42, B_41))), inference(superposition, [status(thm), theory('equality')], [c_8, c_72])).
% 3.98/1.66  tff(c_12, plain, (![A_14, B_15]: (k1_setfam_1(k2_tarski(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.98/1.66  tff(c_98, plain, (![B_41, A_42]: (k3_xboole_0(B_41, A_42)=k3_xboole_0(A_42, B_41))), inference(superposition, [status(thm), theory('equality')], [c_92, c_12])).
% 3.98/1.66  tff(c_164, plain, (![A_47, C_48, B_49]: (r1_tarski(k3_xboole_0(A_47, C_48), B_49) | ~r1_tarski(A_47, B_49))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.98/1.66  tff(c_170, plain, (![A_42, B_41, B_49]: (r1_tarski(k3_xboole_0(A_42, B_41), B_49) | ~r1_tarski(B_41, B_49))), inference(superposition, [status(thm), theory('equality')], [c_98, c_164])).
% 3.98/1.66  tff(c_16, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.98/1.66  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.98/1.66  tff(c_115, plain, (![B_43, A_44]: (k3_xboole_0(B_43, A_44)=k3_xboole_0(A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_92, c_12])).
% 3.98/1.66  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k3_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.98/1.66  tff(c_130, plain, (![B_43, A_44]: (r1_tarski(k3_xboole_0(B_43, A_44), A_44))), inference(superposition, [status(thm), theory('equality')], [c_115, c_4])).
% 3.98/1.66  tff(c_20, plain, (![A_20, B_24, C_26]: (r1_tarski(k2_pre_topc(A_20, B_24), k2_pre_topc(A_20, C_26)) | ~r1_tarski(B_24, C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(u1_struct_0(A_20))) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.98/1.66  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.98/1.66  tff(c_6, plain, (![A_6, B_7, C_8]: (r1_tarski(A_6, k3_xboole_0(B_7, C_8)) | ~r1_tarski(A_6, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.98/1.66  tff(c_240, plain, (![A_64, B_65]: (m1_subset_1(k2_pre_topc(A_64, B_65), k1_zfmisc_1(u1_struct_0(A_64))) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.98/1.66  tff(c_10, plain, (![A_11, B_12, C_13]: (k9_subset_1(A_11, B_12, C_13)=k3_xboole_0(B_12, C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.98/1.66  tff(c_1301, plain, (![A_106, B_107, B_108]: (k9_subset_1(u1_struct_0(A_106), B_107, k2_pre_topc(A_106, B_108))=k3_xboole_0(B_107, k2_pre_topc(A_106, B_108)) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(resolution, [status(thm)], [c_240, c_10])).
% 3.98/1.66  tff(c_1308, plain, (![B_107]: (k9_subset_1(u1_struct_0('#skF_1'), B_107, k2_pre_topc('#skF_1', '#skF_3'))=k3_xboole_0(B_107, k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_1301])).
% 3.98/1.66  tff(c_1315, plain, (![B_107]: (k9_subset_1(u1_struct_0('#skF_1'), B_107, k2_pre_topc('#skF_1', '#skF_3'))=k3_xboole_0(B_107, k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1308])).
% 3.98/1.66  tff(c_179, plain, (![A_53, B_54, C_55]: (k9_subset_1(A_53, B_54, C_55)=k3_xboole_0(B_54, C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.98/1.66  tff(c_187, plain, (![B_54]: (k9_subset_1(u1_struct_0('#skF_1'), B_54, '#skF_3')=k3_xboole_0(B_54, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_179])).
% 3.98/1.66  tff(c_22, plain, (~r1_tarski(k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.98/1.66  tff(c_189, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_22])).
% 3.98/1.66  tff(c_190, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_189])).
% 3.98/1.66  tff(c_1319, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1315, c_190])).
% 3.98/1.66  tff(c_1320, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_1319])).
% 3.98/1.66  tff(c_1342, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k2_pre_topc('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_6, c_1320])).
% 3.98/1.66  tff(c_1721, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k2_pre_topc('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1342])).
% 3.98/1.66  tff(c_1724, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_1721])).
% 3.98/1.66  tff(c_1727, plain, (~m1_subset_1(k3_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_4, c_1724])).
% 3.98/1.66  tff(c_1731, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_1727])).
% 3.98/1.66  tff(c_1734, plain, (~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_170, c_1731])).
% 3.98/1.66  tff(c_1741, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_1734])).
% 3.98/1.66  tff(c_1742, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_1342])).
% 3.98/1.66  tff(c_1746, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_1742])).
% 3.98/1.66  tff(c_1749, plain, (~m1_subset_1(k3_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_130, c_1746])).
% 3.98/1.66  tff(c_1753, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_1749])).
% 3.98/1.66  tff(c_1835, plain, (~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_170, c_1753])).
% 3.98/1.66  tff(c_1842, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_1835])).
% 3.98/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/1.66  
% 3.98/1.66  Inference rules
% 3.98/1.66  ----------------------
% 3.98/1.66  #Ref     : 0
% 3.98/1.66  #Sup     : 492
% 3.98/1.66  #Fact    : 0
% 3.98/1.66  #Define  : 0
% 3.98/1.66  #Split   : 1
% 3.98/1.66  #Chain   : 0
% 3.98/1.66  #Close   : 0
% 3.98/1.66  
% 3.98/1.66  Ordering : KBO
% 3.98/1.66  
% 3.98/1.66  Simplification rules
% 3.98/1.66  ----------------------
% 3.98/1.66  #Subsume      : 86
% 3.98/1.66  #Demod        : 91
% 3.98/1.66  #Tautology    : 160
% 3.98/1.66  #SimpNegUnit  : 0
% 3.98/1.66  #BackRed      : 2
% 3.98/1.66  
% 3.98/1.66  #Partial instantiations: 0
% 3.98/1.66  #Strategies tried      : 1
% 3.98/1.66  
% 3.98/1.66  Timing (in seconds)
% 3.98/1.66  ----------------------
% 3.98/1.66  Preprocessing        : 0.30
% 3.98/1.66  Parsing              : 0.17
% 3.98/1.66  CNF conversion       : 0.02
% 3.98/1.66  Main loop            : 0.60
% 3.98/1.66  Inferencing          : 0.19
% 3.98/1.66  Reduction            : 0.26
% 3.98/1.66  Demodulation         : 0.23
% 3.98/1.66  BG Simplification    : 0.03
% 3.98/1.66  Subsumption          : 0.08
% 3.98/1.66  Abstraction          : 0.03
% 3.98/1.66  MUC search           : 0.00
% 3.98/1.66  Cooper               : 0.00
% 3.98/1.66  Total                : 0.93
% 3.98/1.66  Index Insertion      : 0.00
% 3.98/1.66  Index Deletion       : 0.00
% 3.98/1.66  Index Matching       : 0.00
% 3.98/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------

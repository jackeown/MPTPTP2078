%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:35 EST 2020

% Result     : Theorem 7.28s
% Output     : CNFRefutation 7.60s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 104 expanded)
%              Number of leaves         :   30 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :   91 ( 145 expanded)
%              Number of equality atoms :   27 (  41 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_struct_0 > k7_subset_1 > k5_setfam_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : k3_tarski(k2_xboole_0(A,B)) = k2_xboole_0(k3_tarski(A),k3_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => r1_tarski(k7_subset_1(u1_struct_0(A),k5_setfam_1(u1_struct_0(A),B),k5_setfam_1(u1_struct_0(A),C)),k5_setfam_1(u1_struct_0(A),k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tops_2)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( r1_tarski(C,B)
             => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_tops_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_10,plain,(
    ! [B_11,A_10] : k2_tarski(B_11,A_10) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_82,plain,(
    ! [A_46,B_47] : k3_tarski(k2_tarski(A_46,B_47)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_110,plain,(
    ! [B_50,A_51] : k3_tarski(k2_tarski(B_50,A_51)) = k2_xboole_0(A_51,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_82])).

tff(c_12,plain,(
    ! [A_12,B_13] : k3_tarski(k2_tarski(A_12,B_13)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_116,plain,(
    ! [B_50,A_51] : k2_xboole_0(B_50,A_51) = k2_xboole_0(A_51,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_12])).

tff(c_252,plain,(
    ! [A_66,B_67] : k2_xboole_0(k3_tarski(A_66),k3_tarski(B_67)) = k3_tarski(k2_xboole_0(A_66,B_67)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_303,plain,(
    ! [A_68,B_69] : r1_tarski(k3_tarski(A_68),k3_tarski(k2_xboole_0(A_68,B_69))) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_8])).

tff(c_315,plain,(
    ! [B_50,A_51] : r1_tarski(k3_tarski(B_50),k3_tarski(k2_xboole_0(A_51,B_50))) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_303])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_16,B_17] : k2_xboole_0(k3_tarski(A_16),k3_tarski(B_17)) = k3_tarski(k2_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski(k4_xboole_0(A_5,B_6),C_7)
      | ~ r1_tarski(A_5,k2_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_133,plain,(
    ! [B_52,A_53] : k2_xboole_0(B_52,A_53) = k2_xboole_0(A_53,B_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_12])).

tff(c_148,plain,(
    ! [A_53,B_52] : r1_tarski(A_53,k2_xboole_0(B_52,A_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_8])).

tff(c_36,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1054,plain,(
    ! [C_106,A_107,B_108] :
      ( m1_subset_1(C_106,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_107))))
      | ~ r1_tarski(C_106,B_108)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_107))))
      | ~ l1_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3213,plain,(
    ! [A_193,B_194,A_195,C_196] :
      ( m1_subset_1(k4_xboole_0(A_193,B_194),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_195))))
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_195))))
      | ~ l1_struct_0(A_195)
      | ~ r1_tarski(A_193,k2_xboole_0(B_194,C_196)) ) ),
    inference(resolution,[status(thm)],[c_6,c_1054])).

tff(c_3222,plain,(
    ! [A_193,B_194] :
      ( m1_subset_1(k4_xboole_0(A_193,B_194),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_struct_0('#skF_1')
      | ~ r1_tarski(A_193,k2_xboole_0(B_194,'#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_34,c_3213])).

tff(c_3266,plain,(
    ! [A_202,B_203] :
      ( m1_subset_1(k4_xboole_0(A_202,B_203),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ r1_tarski(A_202,k2_xboole_0(B_203,'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3222])).

tff(c_22,plain,(
    ! [A_22,B_23] :
      ( k5_setfam_1(A_22,B_23) = k3_tarski(B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(k1_zfmisc_1(A_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3281,plain,(
    ! [A_202,B_203] :
      ( k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0(A_202,B_203)) = k3_tarski(k4_xboole_0(A_202,B_203))
      | ~ r1_tarski(A_202,k2_xboole_0(B_203,'#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_3266,c_22])).

tff(c_97,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | ~ m1_subset_1(A_48,k1_zfmisc_1(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_109,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_34,c_97])).

tff(c_18,plain,(
    ! [A_18] : k3_tarski(k1_zfmisc_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_172,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(k3_tarski(A_54),k3_tarski(B_55))
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_190,plain,(
    ! [A_54,A_18] :
      ( r1_tarski(k3_tarski(A_54),A_18)
      | ~ r1_tarski(A_54,k1_zfmisc_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_172])).

tff(c_26,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(A_24,k1_zfmisc_1(B_25))
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_569,plain,(
    ! [A_91,B_92,C_93] :
      ( k7_subset_1(A_91,B_92,C_93) = k4_xboole_0(B_92,C_93)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1226,plain,(
    ! [B_112,A_113,C_114] :
      ( k7_subset_1(B_112,A_113,C_114) = k4_xboole_0(A_113,C_114)
      | ~ r1_tarski(A_113,B_112) ) ),
    inference(resolution,[status(thm)],[c_26,c_569])).

tff(c_7411,plain,(
    ! [A_310,A_311,C_312] :
      ( k7_subset_1(A_310,k3_tarski(A_311),C_312) = k4_xboole_0(k3_tarski(A_311),C_312)
      | ~ r1_tarski(A_311,k1_zfmisc_1(A_310)) ) ),
    inference(resolution,[status(thm)],[c_190,c_1226])).

tff(c_7433,plain,(
    ! [C_312] : k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),C_312) = k4_xboole_0(k3_tarski('#skF_2'),C_312) ),
    inference(resolution,[status(thm)],[c_109,c_7411])).

tff(c_578,plain,(
    ! [C_93] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_93) = k4_xboole_0('#skF_2',C_93) ),
    inference(resolution,[status(thm)],[c_34,c_569])).

tff(c_391,plain,(
    ! [A_79,B_80] :
      ( k5_setfam_1(A_79,B_80) = k3_tarski(B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k1_zfmisc_1(A_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_404,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_391])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_403,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3') = k3_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_391])).

tff(c_30,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_405,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_30])).

tff(c_415,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_405])).

tff(c_588,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_578,c_415])).

tff(c_7436,plain,(
    ~ r1_tarski(k4_xboole_0(k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7433,c_588])).

tff(c_7458,plain,
    ( ~ r1_tarski(k4_xboole_0(k3_tarski('#skF_2'),k3_tarski('#skF_3')),k3_tarski(k4_xboole_0('#skF_2','#skF_3')))
    | ~ r1_tarski('#skF_2',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3281,c_7436])).

tff(c_7466,plain,(
    ~ r1_tarski(k4_xboole_0(k3_tarski('#skF_2'),k3_tarski('#skF_3')),k3_tarski(k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_7458])).

tff(c_7470,plain,(
    ~ r1_tarski(k3_tarski('#skF_2'),k2_xboole_0(k3_tarski('#skF_3'),k3_tarski(k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(resolution,[status(thm)],[c_6,c_7466])).

tff(c_7474,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_4,c_16,c_7470])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:06:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.28/2.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.28/2.58  
% 7.28/2.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.28/2.59  %$ r1_tarski > m1_subset_1 > l1_struct_0 > k7_subset_1 > k5_setfam_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 7.28/2.59  
% 7.28/2.59  %Foreground sorts:
% 7.28/2.59  
% 7.28/2.59  
% 7.28/2.59  %Background operators:
% 7.28/2.59  
% 7.28/2.59  
% 7.28/2.59  %Foreground operators:
% 7.28/2.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.28/2.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.28/2.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.28/2.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.28/2.59  tff('#skF_2', type, '#skF_2': $i).
% 7.28/2.59  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 7.28/2.59  tff('#skF_3', type, '#skF_3': $i).
% 7.28/2.59  tff('#skF_1', type, '#skF_1': $i).
% 7.28/2.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.28/2.59  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.28/2.59  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 7.28/2.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.28/2.59  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.28/2.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.28/2.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.28/2.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.28/2.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.28/2.59  
% 7.60/2.60  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.60/2.60  tff(f_39, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 7.60/2.60  tff(f_45, axiom, (![A, B]: (k3_tarski(k2_xboole_0(A, B)) = k2_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 7.60/2.60  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.60/2.60  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 7.60/2.60  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 7.60/2.60  tff(f_80, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => r1_tarski(k7_subset_1(u1_struct_0(A), k5_setfam_1(u1_struct_0(A), B), k5_setfam_1(u1_struct_0(A), C)), k5_setfam_1(u1_struct_0(A), k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tops_2)).
% 7.60/2.60  tff(f_69, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (r1_tarski(C, B) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_tops_2)).
% 7.60/2.60  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 7.60/2.60  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.60/2.60  tff(f_47, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 7.60/2.60  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 7.60/2.60  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 7.60/2.60  tff(c_10, plain, (![B_11, A_10]: (k2_tarski(B_11, A_10)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.60/2.60  tff(c_82, plain, (![A_46, B_47]: (k3_tarski(k2_tarski(A_46, B_47))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.60/2.60  tff(c_110, plain, (![B_50, A_51]: (k3_tarski(k2_tarski(B_50, A_51))=k2_xboole_0(A_51, B_50))), inference(superposition, [status(thm), theory('equality')], [c_10, c_82])).
% 7.60/2.60  tff(c_12, plain, (![A_12, B_13]: (k3_tarski(k2_tarski(A_12, B_13))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.60/2.60  tff(c_116, plain, (![B_50, A_51]: (k2_xboole_0(B_50, A_51)=k2_xboole_0(A_51, B_50))), inference(superposition, [status(thm), theory('equality')], [c_110, c_12])).
% 7.60/2.60  tff(c_252, plain, (![A_66, B_67]: (k2_xboole_0(k3_tarski(A_66), k3_tarski(B_67))=k3_tarski(k2_xboole_0(A_66, B_67)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.60/2.60  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.60/2.60  tff(c_303, plain, (![A_68, B_69]: (r1_tarski(k3_tarski(A_68), k3_tarski(k2_xboole_0(A_68, B_69))))), inference(superposition, [status(thm), theory('equality')], [c_252, c_8])).
% 7.60/2.60  tff(c_315, plain, (![B_50, A_51]: (r1_tarski(k3_tarski(B_50), k3_tarski(k2_xboole_0(A_51, B_50))))), inference(superposition, [status(thm), theory('equality')], [c_116, c_303])).
% 7.60/2.60  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.60/2.60  tff(c_16, plain, (![A_16, B_17]: (k2_xboole_0(k3_tarski(A_16), k3_tarski(B_17))=k3_tarski(k2_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.60/2.60  tff(c_6, plain, (![A_5, B_6, C_7]: (r1_tarski(k4_xboole_0(A_5, B_6), C_7) | ~r1_tarski(A_5, k2_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.60/2.60  tff(c_133, plain, (![B_52, A_53]: (k2_xboole_0(B_52, A_53)=k2_xboole_0(A_53, B_52))), inference(superposition, [status(thm), theory('equality')], [c_110, c_12])).
% 7.60/2.60  tff(c_148, plain, (![A_53, B_52]: (r1_tarski(A_53, k2_xboole_0(B_52, A_53)))), inference(superposition, [status(thm), theory('equality')], [c_133, c_8])).
% 7.60/2.60  tff(c_36, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.60/2.60  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.60/2.60  tff(c_1054, plain, (![C_106, A_107, B_108]: (m1_subset_1(C_106, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_107)))) | ~r1_tarski(C_106, B_108) | ~m1_subset_1(B_108, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_107)))) | ~l1_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.60/2.60  tff(c_3213, plain, (![A_193, B_194, A_195, C_196]: (m1_subset_1(k4_xboole_0(A_193, B_194), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_195)))) | ~m1_subset_1(C_196, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_195)))) | ~l1_struct_0(A_195) | ~r1_tarski(A_193, k2_xboole_0(B_194, C_196)))), inference(resolution, [status(thm)], [c_6, c_1054])).
% 7.60/2.60  tff(c_3222, plain, (![A_193, B_194]: (m1_subset_1(k4_xboole_0(A_193, B_194), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_struct_0('#skF_1') | ~r1_tarski(A_193, k2_xboole_0(B_194, '#skF_2')))), inference(resolution, [status(thm)], [c_34, c_3213])).
% 7.60/2.60  tff(c_3266, plain, (![A_202, B_203]: (m1_subset_1(k4_xboole_0(A_202, B_203), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~r1_tarski(A_202, k2_xboole_0(B_203, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3222])).
% 7.60/2.60  tff(c_22, plain, (![A_22, B_23]: (k5_setfam_1(A_22, B_23)=k3_tarski(B_23) | ~m1_subset_1(B_23, k1_zfmisc_1(k1_zfmisc_1(A_22))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.60/2.60  tff(c_3281, plain, (![A_202, B_203]: (k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0(A_202, B_203))=k3_tarski(k4_xboole_0(A_202, B_203)) | ~r1_tarski(A_202, k2_xboole_0(B_203, '#skF_2')))), inference(resolution, [status(thm)], [c_3266, c_22])).
% 7.60/2.60  tff(c_97, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | ~m1_subset_1(A_48, k1_zfmisc_1(B_49)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.60/2.60  tff(c_109, plain, (r1_tarski('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_34, c_97])).
% 7.60/2.60  tff(c_18, plain, (![A_18]: (k3_tarski(k1_zfmisc_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.60/2.60  tff(c_172, plain, (![A_54, B_55]: (r1_tarski(k3_tarski(A_54), k3_tarski(B_55)) | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.60/2.60  tff(c_190, plain, (![A_54, A_18]: (r1_tarski(k3_tarski(A_54), A_18) | ~r1_tarski(A_54, k1_zfmisc_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_172])).
% 7.60/2.60  tff(c_26, plain, (![A_24, B_25]: (m1_subset_1(A_24, k1_zfmisc_1(B_25)) | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.60/2.60  tff(c_569, plain, (![A_91, B_92, C_93]: (k7_subset_1(A_91, B_92, C_93)=k4_xboole_0(B_92, C_93) | ~m1_subset_1(B_92, k1_zfmisc_1(A_91)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.60/2.60  tff(c_1226, plain, (![B_112, A_113, C_114]: (k7_subset_1(B_112, A_113, C_114)=k4_xboole_0(A_113, C_114) | ~r1_tarski(A_113, B_112))), inference(resolution, [status(thm)], [c_26, c_569])).
% 7.60/2.60  tff(c_7411, plain, (![A_310, A_311, C_312]: (k7_subset_1(A_310, k3_tarski(A_311), C_312)=k4_xboole_0(k3_tarski(A_311), C_312) | ~r1_tarski(A_311, k1_zfmisc_1(A_310)))), inference(resolution, [status(thm)], [c_190, c_1226])).
% 7.60/2.60  tff(c_7433, plain, (![C_312]: (k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), C_312)=k4_xboole_0(k3_tarski('#skF_2'), C_312))), inference(resolution, [status(thm)], [c_109, c_7411])).
% 7.60/2.60  tff(c_578, plain, (![C_93]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_93)=k4_xboole_0('#skF_2', C_93))), inference(resolution, [status(thm)], [c_34, c_569])).
% 7.60/2.60  tff(c_391, plain, (![A_79, B_80]: (k5_setfam_1(A_79, B_80)=k3_tarski(B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(k1_zfmisc_1(A_79))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.60/2.60  tff(c_404, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2')=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_34, c_391])).
% 7.60/2.60  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.60/2.60  tff(c_403, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')=k3_tarski('#skF_3')), inference(resolution, [status(thm)], [c_32, c_391])).
% 7.60/2.60  tff(c_30, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.60/2.60  tff(c_405, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_403, c_30])).
% 7.60/2.60  tff(c_415, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_404, c_405])).
% 7.60/2.60  tff(c_588, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_578, c_415])).
% 7.60/2.60  tff(c_7436, plain, (~r1_tarski(k4_xboole_0(k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_7433, c_588])).
% 7.60/2.60  tff(c_7458, plain, (~r1_tarski(k4_xboole_0(k3_tarski('#skF_2'), k3_tarski('#skF_3')), k3_tarski(k4_xboole_0('#skF_2', '#skF_3'))) | ~r1_tarski('#skF_2', k2_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3281, c_7436])).
% 7.60/2.60  tff(c_7466, plain, (~r1_tarski(k4_xboole_0(k3_tarski('#skF_2'), k3_tarski('#skF_3')), k3_tarski(k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_7458])).
% 7.60/2.60  tff(c_7470, plain, (~r1_tarski(k3_tarski('#skF_2'), k2_xboole_0(k3_tarski('#skF_3'), k3_tarski(k4_xboole_0('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_6, c_7466])).
% 7.60/2.60  tff(c_7474, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_315, c_4, c_16, c_7470])).
% 7.60/2.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.60/2.60  
% 7.60/2.60  Inference rules
% 7.60/2.60  ----------------------
% 7.60/2.60  #Ref     : 0
% 7.60/2.60  #Sup     : 2068
% 7.60/2.60  #Fact    : 0
% 7.60/2.60  #Define  : 0
% 7.60/2.60  #Split   : 1
% 7.60/2.60  #Chain   : 0
% 7.60/2.60  #Close   : 0
% 7.60/2.60  
% 7.60/2.60  Ordering : KBO
% 7.60/2.60  
% 7.60/2.60  Simplification rules
% 7.60/2.60  ----------------------
% 7.60/2.60  #Subsume      : 47
% 7.60/2.60  #Demod        : 990
% 7.60/2.60  #Tautology    : 670
% 7.60/2.60  #SimpNegUnit  : 0
% 7.60/2.60  #BackRed      : 5
% 7.60/2.60  
% 7.60/2.60  #Partial instantiations: 0
% 7.60/2.60  #Strategies tried      : 1
% 7.60/2.60  
% 7.60/2.60  Timing (in seconds)
% 7.60/2.60  ----------------------
% 7.60/2.60  Preprocessing        : 0.32
% 7.60/2.60  Parsing              : 0.17
% 7.60/2.60  CNF conversion       : 0.02
% 7.60/2.60  Main loop            : 1.53
% 7.60/2.60  Inferencing          : 0.34
% 7.60/2.61  Reduction            : 0.78
% 7.60/2.61  Demodulation         : 0.68
% 7.60/2.61  BG Simplification    : 0.05
% 7.60/2.61  Subsumption          : 0.27
% 7.60/2.61  Abstraction          : 0.06
% 7.60/2.61  MUC search           : 0.00
% 7.60/2.61  Cooper               : 0.00
% 7.60/2.61  Total                : 1.89
% 7.60/2.61  Index Insertion      : 0.00
% 7.60/2.61  Index Deletion       : 0.00
% 7.60/2.61  Index Matching       : 0.00
% 7.60/2.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------

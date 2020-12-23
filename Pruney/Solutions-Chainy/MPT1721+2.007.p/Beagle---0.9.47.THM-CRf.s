%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:44 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   56 (  79 expanded)
%              Number of leaves         :   22 (  40 expanded)
%              Depth                    :   15
%              Number of atoms          :  219 ( 445 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k2_tsep_1 > k3_xboole_0 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_tsep_1,type,(
    k2_tsep_1: ( $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_131,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ( ( m1_pre_topc(B,D)
                        & m1_pre_topc(C,D) )
                     => ( r1_tsep_1(B,C)
                        | m1_pre_topc(k2_tsep_1(A,B,C),D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tmap_1)).

tff(f_97,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k2_tsep_1(A,B,C))
        & v1_pre_topc(k2_tsep_1(A,B,C))
        & m1_pre_topc(k2_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( ~ r1_tsep_1(B,C)
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & v1_pre_topc(D)
                      & m1_pre_topc(D,A) )
                   => ( D = k2_tsep_1(A,B,C)
                    <=> u1_struct_0(D) = k3_xboole_0(u1_struct_0(B),u1_struct_0(C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tsep_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_20,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_34,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_24,plain,(
    m1_pre_topc('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_30,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_26,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_45,plain,(
    ! [B_46,C_47,A_48] :
      ( r1_tarski(u1_struct_0(B_46),u1_struct_0(C_47))
      | ~ m1_pre_topc(B_46,C_47)
      | ~ m1_pre_topc(C_47,A_48)
      | ~ m1_pre_topc(B_46,A_48)
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_53,plain,(
    ! [B_46] :
      ( r1_tarski(u1_struct_0(B_46),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_46,'#skF_4')
      | ~ m1_pre_topc(B_46,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_45])).

tff(c_63,plain,(
    ! [B_46] :
      ( r1_tarski(u1_struct_0(B_46),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_46,'#skF_4')
      | ~ m1_pre_topc(B_46,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_53])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_8,plain,(
    ! [A_19,B_20,C_21] :
      ( m1_pre_topc(k2_tsep_1(A_19,B_20,C_21),A_19)
      | ~ m1_pre_topc(C_21,A_19)
      | v2_struct_0(C_21)
      | ~ m1_pre_topc(B_20,A_19)
      | v2_struct_0(B_20)
      | ~ l1_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_10,plain,(
    ! [A_19,B_20,C_21] :
      ( v1_pre_topc(k2_tsep_1(A_19,B_20,C_21))
      | ~ m1_pre_topc(C_21,A_19)
      | v2_struct_0(C_21)
      | ~ m1_pre_topc(B_20,A_19)
      | v2_struct_0(B_20)
      | ~ l1_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_91,plain,(
    ! [A_69,B_70,C_71] :
      ( u1_struct_0(k2_tsep_1(A_69,B_70,C_71)) = k3_xboole_0(u1_struct_0(B_70),u1_struct_0(C_71))
      | ~ m1_pre_topc(k2_tsep_1(A_69,B_70,C_71),A_69)
      | ~ v1_pre_topc(k2_tsep_1(A_69,B_70,C_71))
      | v2_struct_0(k2_tsep_1(A_69,B_70,C_71))
      | r1_tsep_1(B_70,C_71)
      | ~ m1_pre_topc(C_71,A_69)
      | v2_struct_0(C_71)
      | ~ m1_pre_topc(B_70,A_69)
      | v2_struct_0(B_70)
      | ~ l1_pre_topc(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_95,plain,(
    ! [A_72,B_73,C_74] :
      ( u1_struct_0(k2_tsep_1(A_72,B_73,C_74)) = k3_xboole_0(u1_struct_0(B_73),u1_struct_0(C_74))
      | ~ v1_pre_topc(k2_tsep_1(A_72,B_73,C_74))
      | v2_struct_0(k2_tsep_1(A_72,B_73,C_74))
      | r1_tsep_1(B_73,C_74)
      | ~ m1_pre_topc(C_74,A_72)
      | v2_struct_0(C_74)
      | ~ m1_pre_topc(B_73,A_72)
      | v2_struct_0(B_73)
      | ~ l1_pre_topc(A_72)
      | v2_struct_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_8,c_91])).

tff(c_12,plain,(
    ! [A_19,B_20,C_21] :
      ( ~ v2_struct_0(k2_tsep_1(A_19,B_20,C_21))
      | ~ m1_pre_topc(C_21,A_19)
      | v2_struct_0(C_21)
      | ~ m1_pre_topc(B_20,A_19)
      | v2_struct_0(B_20)
      | ~ l1_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_164,plain,(
    ! [A_78,B_79,C_80] :
      ( u1_struct_0(k2_tsep_1(A_78,B_79,C_80)) = k3_xboole_0(u1_struct_0(B_79),u1_struct_0(C_80))
      | ~ v1_pre_topc(k2_tsep_1(A_78,B_79,C_80))
      | r1_tsep_1(B_79,C_80)
      | ~ m1_pre_topc(C_80,A_78)
      | v2_struct_0(C_80)
      | ~ m1_pre_topc(B_79,A_78)
      | v2_struct_0(B_79)
      | ~ l1_pre_topc(A_78)
      | v2_struct_0(A_78) ) ),
    inference(resolution,[status(thm)],[c_95,c_12])).

tff(c_168,plain,(
    ! [A_81,B_82,C_83] :
      ( u1_struct_0(k2_tsep_1(A_81,B_82,C_83)) = k3_xboole_0(u1_struct_0(B_82),u1_struct_0(C_83))
      | r1_tsep_1(B_82,C_83)
      | ~ m1_pre_topc(C_83,A_81)
      | v2_struct_0(C_83)
      | ~ m1_pre_topc(B_82,A_81)
      | v2_struct_0(B_82)
      | ~ l1_pre_topc(A_81)
      | v2_struct_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_10,c_164])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(k3_xboole_0(A_1,C_3),B_2)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_225,plain,(
    ! [A_84,B_85,C_86,B_87] :
      ( r1_tarski(u1_struct_0(k2_tsep_1(A_84,B_85,C_86)),B_87)
      | ~ r1_tarski(u1_struct_0(B_85),B_87)
      | r1_tsep_1(B_85,C_86)
      | ~ m1_pre_topc(C_86,A_84)
      | v2_struct_0(C_86)
      | ~ m1_pre_topc(B_85,A_84)
      | v2_struct_0(B_85)
      | ~ l1_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_2])).

tff(c_16,plain,(
    ! [B_26,C_28,A_22] :
      ( m1_pre_topc(B_26,C_28)
      | ~ r1_tarski(u1_struct_0(B_26),u1_struct_0(C_28))
      | ~ m1_pre_topc(C_28,A_22)
      | ~ m1_pre_topc(B_26,A_22)
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_277,plain,(
    ! [B_104,A_102,C_105,C_101,A_103] :
      ( m1_pre_topc(k2_tsep_1(A_103,B_104,C_101),C_105)
      | ~ m1_pre_topc(C_105,A_102)
      | ~ m1_pre_topc(k2_tsep_1(A_103,B_104,C_101),A_102)
      | ~ l1_pre_topc(A_102)
      | ~ v2_pre_topc(A_102)
      | ~ r1_tarski(u1_struct_0(B_104),u1_struct_0(C_105))
      | r1_tsep_1(B_104,C_101)
      | ~ m1_pre_topc(C_101,A_103)
      | v2_struct_0(C_101)
      | ~ m1_pre_topc(B_104,A_103)
      | v2_struct_0(B_104)
      | ~ l1_pre_topc(A_103)
      | v2_struct_0(A_103) ) ),
    inference(resolution,[status(thm)],[c_225,c_16])).

tff(c_287,plain,(
    ! [A_103,B_104,C_101] :
      ( m1_pre_topc(k2_tsep_1(A_103,B_104,C_101),'#skF_4')
      | ~ m1_pre_topc(k2_tsep_1(A_103,B_104,C_101),'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(u1_struct_0(B_104),u1_struct_0('#skF_4'))
      | r1_tsep_1(B_104,C_101)
      | ~ m1_pre_topc(C_101,A_103)
      | v2_struct_0(C_101)
      | ~ m1_pre_topc(B_104,A_103)
      | v2_struct_0(B_104)
      | ~ l1_pre_topc(A_103)
      | v2_struct_0(A_103) ) ),
    inference(resolution,[status(thm)],[c_26,c_277])).

tff(c_312,plain,(
    ! [A_109,B_110,C_111] :
      ( m1_pre_topc(k2_tsep_1(A_109,B_110,C_111),'#skF_4')
      | ~ m1_pre_topc(k2_tsep_1(A_109,B_110,C_111),'#skF_1')
      | ~ r1_tarski(u1_struct_0(B_110),u1_struct_0('#skF_4'))
      | r1_tsep_1(B_110,C_111)
      | ~ m1_pre_topc(C_111,A_109)
      | v2_struct_0(C_111)
      | ~ m1_pre_topc(B_110,A_109)
      | v2_struct_0(B_110)
      | ~ l1_pre_topc(A_109)
      | v2_struct_0(A_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_287])).

tff(c_315,plain,(
    ! [B_20,C_21] :
      ( m1_pre_topc(k2_tsep_1('#skF_1',B_20,C_21),'#skF_4')
      | ~ r1_tarski(u1_struct_0(B_20),u1_struct_0('#skF_4'))
      | r1_tsep_1(B_20,C_21)
      | ~ m1_pre_topc(C_21,'#skF_1')
      | v2_struct_0(C_21)
      | ~ m1_pre_topc(B_20,'#skF_1')
      | v2_struct_0(B_20)
      | ~ l1_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_8,c_312])).

tff(c_318,plain,(
    ! [B_20,C_21] :
      ( m1_pre_topc(k2_tsep_1('#skF_1',B_20,C_21),'#skF_4')
      | ~ r1_tarski(u1_struct_0(B_20),u1_struct_0('#skF_4'))
      | r1_tsep_1(B_20,C_21)
      | ~ m1_pre_topc(C_21,'#skF_1')
      | v2_struct_0(C_21)
      | ~ m1_pre_topc(B_20,'#skF_1')
      | v2_struct_0(B_20)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_315])).

tff(c_320,plain,(
    ! [B_112,C_113] :
      ( m1_pre_topc(k2_tsep_1('#skF_1',B_112,C_113),'#skF_4')
      | ~ r1_tarski(u1_struct_0(B_112),u1_struct_0('#skF_4'))
      | r1_tsep_1(B_112,C_113)
      | ~ m1_pre_topc(C_113,'#skF_1')
      | v2_struct_0(C_113)
      | ~ m1_pre_topc(B_112,'#skF_1')
      | v2_struct_0(B_112) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_318])).

tff(c_330,plain,(
    ! [B_114,C_115] :
      ( m1_pre_topc(k2_tsep_1('#skF_1',B_114,C_115),'#skF_4')
      | r1_tsep_1(B_114,C_115)
      | ~ m1_pre_topc(C_115,'#skF_1')
      | v2_struct_0(C_115)
      | v2_struct_0(B_114)
      | ~ m1_pre_topc(B_114,'#skF_4')
      | ~ m1_pre_topc(B_114,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_63,c_320])).

tff(c_18,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_337,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_330,c_18])).

tff(c_342,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_24,c_30,c_337])).

tff(c_344,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_32,c_20,c_342])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:24:25 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.39  
% 2.86/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.39  %$ r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k2_tsep_1 > k3_xboole_0 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.86/1.39  
% 2.86/1.39  %Foreground sorts:
% 2.86/1.39  
% 2.86/1.39  
% 2.86/1.39  %Background operators:
% 2.86/1.39  
% 2.86/1.39  
% 2.86/1.39  %Foreground operators:
% 2.86/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.86/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.86/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.86/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.86/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.86/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.86/1.39  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.86/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.86/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.39  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.86/1.39  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 2.86/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.86/1.39  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.86/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.86/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.86/1.39  
% 2.86/1.40  tff(f_131, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((m1_pre_topc(B, D) & m1_pre_topc(C, D)) => (r1_tsep_1(B, C) | m1_pre_topc(k2_tsep_1(A, B, C), D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_tmap_1)).
% 2.86/1.40  tff(f_97, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 2.86/1.40  tff(f_83, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k2_tsep_1(A, B, C)) & v1_pre_topc(k2_tsep_1(A, B, C))) & m1_pre_topc(k2_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 2.86/1.40  tff(f_61, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (~r1_tsep_1(B, C) => (![D]: (((~v2_struct_0(D) & v1_pre_topc(D)) & m1_pre_topc(D, A)) => ((D = k2_tsep_1(A, B, C)) <=> (u1_struct_0(D) = k3_xboole_0(u1_struct_0(B), u1_struct_0(C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tsep_1)).
% 2.86/1.40  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 2.86/1.40  tff(c_36, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.86/1.40  tff(c_32, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.86/1.40  tff(c_20, plain, (~r1_tsep_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.86/1.40  tff(c_34, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.86/1.40  tff(c_24, plain, (m1_pre_topc('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.86/1.40  tff(c_30, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.86/1.40  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.86/1.40  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.86/1.40  tff(c_26, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.86/1.40  tff(c_45, plain, (![B_46, C_47, A_48]: (r1_tarski(u1_struct_0(B_46), u1_struct_0(C_47)) | ~m1_pre_topc(B_46, C_47) | ~m1_pre_topc(C_47, A_48) | ~m1_pre_topc(B_46, A_48) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.86/1.40  tff(c_53, plain, (![B_46]: (r1_tarski(u1_struct_0(B_46), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_46, '#skF_4') | ~m1_pre_topc(B_46, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_45])).
% 2.86/1.40  tff(c_63, plain, (![B_46]: (r1_tarski(u1_struct_0(B_46), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_46, '#skF_4') | ~m1_pre_topc(B_46, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_53])).
% 2.86/1.40  tff(c_42, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.86/1.40  tff(c_8, plain, (![A_19, B_20, C_21]: (m1_pre_topc(k2_tsep_1(A_19, B_20, C_21), A_19) | ~m1_pre_topc(C_21, A_19) | v2_struct_0(C_21) | ~m1_pre_topc(B_20, A_19) | v2_struct_0(B_20) | ~l1_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.86/1.40  tff(c_10, plain, (![A_19, B_20, C_21]: (v1_pre_topc(k2_tsep_1(A_19, B_20, C_21)) | ~m1_pre_topc(C_21, A_19) | v2_struct_0(C_21) | ~m1_pre_topc(B_20, A_19) | v2_struct_0(B_20) | ~l1_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.86/1.40  tff(c_91, plain, (![A_69, B_70, C_71]: (u1_struct_0(k2_tsep_1(A_69, B_70, C_71))=k3_xboole_0(u1_struct_0(B_70), u1_struct_0(C_71)) | ~m1_pre_topc(k2_tsep_1(A_69, B_70, C_71), A_69) | ~v1_pre_topc(k2_tsep_1(A_69, B_70, C_71)) | v2_struct_0(k2_tsep_1(A_69, B_70, C_71)) | r1_tsep_1(B_70, C_71) | ~m1_pre_topc(C_71, A_69) | v2_struct_0(C_71) | ~m1_pre_topc(B_70, A_69) | v2_struct_0(B_70) | ~l1_pre_topc(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.86/1.40  tff(c_95, plain, (![A_72, B_73, C_74]: (u1_struct_0(k2_tsep_1(A_72, B_73, C_74))=k3_xboole_0(u1_struct_0(B_73), u1_struct_0(C_74)) | ~v1_pre_topc(k2_tsep_1(A_72, B_73, C_74)) | v2_struct_0(k2_tsep_1(A_72, B_73, C_74)) | r1_tsep_1(B_73, C_74) | ~m1_pre_topc(C_74, A_72) | v2_struct_0(C_74) | ~m1_pre_topc(B_73, A_72) | v2_struct_0(B_73) | ~l1_pre_topc(A_72) | v2_struct_0(A_72))), inference(resolution, [status(thm)], [c_8, c_91])).
% 2.86/1.40  tff(c_12, plain, (![A_19, B_20, C_21]: (~v2_struct_0(k2_tsep_1(A_19, B_20, C_21)) | ~m1_pre_topc(C_21, A_19) | v2_struct_0(C_21) | ~m1_pre_topc(B_20, A_19) | v2_struct_0(B_20) | ~l1_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.86/1.40  tff(c_164, plain, (![A_78, B_79, C_80]: (u1_struct_0(k2_tsep_1(A_78, B_79, C_80))=k3_xboole_0(u1_struct_0(B_79), u1_struct_0(C_80)) | ~v1_pre_topc(k2_tsep_1(A_78, B_79, C_80)) | r1_tsep_1(B_79, C_80) | ~m1_pre_topc(C_80, A_78) | v2_struct_0(C_80) | ~m1_pre_topc(B_79, A_78) | v2_struct_0(B_79) | ~l1_pre_topc(A_78) | v2_struct_0(A_78))), inference(resolution, [status(thm)], [c_95, c_12])).
% 2.86/1.40  tff(c_168, plain, (![A_81, B_82, C_83]: (u1_struct_0(k2_tsep_1(A_81, B_82, C_83))=k3_xboole_0(u1_struct_0(B_82), u1_struct_0(C_83)) | r1_tsep_1(B_82, C_83) | ~m1_pre_topc(C_83, A_81) | v2_struct_0(C_83) | ~m1_pre_topc(B_82, A_81) | v2_struct_0(B_82) | ~l1_pre_topc(A_81) | v2_struct_0(A_81))), inference(resolution, [status(thm)], [c_10, c_164])).
% 2.86/1.40  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(k3_xboole_0(A_1, C_3), B_2) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.86/1.40  tff(c_225, plain, (![A_84, B_85, C_86, B_87]: (r1_tarski(u1_struct_0(k2_tsep_1(A_84, B_85, C_86)), B_87) | ~r1_tarski(u1_struct_0(B_85), B_87) | r1_tsep_1(B_85, C_86) | ~m1_pre_topc(C_86, A_84) | v2_struct_0(C_86) | ~m1_pre_topc(B_85, A_84) | v2_struct_0(B_85) | ~l1_pre_topc(A_84) | v2_struct_0(A_84))), inference(superposition, [status(thm), theory('equality')], [c_168, c_2])).
% 2.86/1.40  tff(c_16, plain, (![B_26, C_28, A_22]: (m1_pre_topc(B_26, C_28) | ~r1_tarski(u1_struct_0(B_26), u1_struct_0(C_28)) | ~m1_pre_topc(C_28, A_22) | ~m1_pre_topc(B_26, A_22) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.86/1.40  tff(c_277, plain, (![B_104, A_102, C_105, C_101, A_103]: (m1_pre_topc(k2_tsep_1(A_103, B_104, C_101), C_105) | ~m1_pre_topc(C_105, A_102) | ~m1_pre_topc(k2_tsep_1(A_103, B_104, C_101), A_102) | ~l1_pre_topc(A_102) | ~v2_pre_topc(A_102) | ~r1_tarski(u1_struct_0(B_104), u1_struct_0(C_105)) | r1_tsep_1(B_104, C_101) | ~m1_pre_topc(C_101, A_103) | v2_struct_0(C_101) | ~m1_pre_topc(B_104, A_103) | v2_struct_0(B_104) | ~l1_pre_topc(A_103) | v2_struct_0(A_103))), inference(resolution, [status(thm)], [c_225, c_16])).
% 2.86/1.40  tff(c_287, plain, (![A_103, B_104, C_101]: (m1_pre_topc(k2_tsep_1(A_103, B_104, C_101), '#skF_4') | ~m1_pre_topc(k2_tsep_1(A_103, B_104, C_101), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(u1_struct_0(B_104), u1_struct_0('#skF_4')) | r1_tsep_1(B_104, C_101) | ~m1_pre_topc(C_101, A_103) | v2_struct_0(C_101) | ~m1_pre_topc(B_104, A_103) | v2_struct_0(B_104) | ~l1_pre_topc(A_103) | v2_struct_0(A_103))), inference(resolution, [status(thm)], [c_26, c_277])).
% 2.86/1.40  tff(c_312, plain, (![A_109, B_110, C_111]: (m1_pre_topc(k2_tsep_1(A_109, B_110, C_111), '#skF_4') | ~m1_pre_topc(k2_tsep_1(A_109, B_110, C_111), '#skF_1') | ~r1_tarski(u1_struct_0(B_110), u1_struct_0('#skF_4')) | r1_tsep_1(B_110, C_111) | ~m1_pre_topc(C_111, A_109) | v2_struct_0(C_111) | ~m1_pre_topc(B_110, A_109) | v2_struct_0(B_110) | ~l1_pre_topc(A_109) | v2_struct_0(A_109))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_287])).
% 2.86/1.40  tff(c_315, plain, (![B_20, C_21]: (m1_pre_topc(k2_tsep_1('#skF_1', B_20, C_21), '#skF_4') | ~r1_tarski(u1_struct_0(B_20), u1_struct_0('#skF_4')) | r1_tsep_1(B_20, C_21) | ~m1_pre_topc(C_21, '#skF_1') | v2_struct_0(C_21) | ~m1_pre_topc(B_20, '#skF_1') | v2_struct_0(B_20) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_312])).
% 2.86/1.40  tff(c_318, plain, (![B_20, C_21]: (m1_pre_topc(k2_tsep_1('#skF_1', B_20, C_21), '#skF_4') | ~r1_tarski(u1_struct_0(B_20), u1_struct_0('#skF_4')) | r1_tsep_1(B_20, C_21) | ~m1_pre_topc(C_21, '#skF_1') | v2_struct_0(C_21) | ~m1_pre_topc(B_20, '#skF_1') | v2_struct_0(B_20) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_315])).
% 2.86/1.40  tff(c_320, plain, (![B_112, C_113]: (m1_pre_topc(k2_tsep_1('#skF_1', B_112, C_113), '#skF_4') | ~r1_tarski(u1_struct_0(B_112), u1_struct_0('#skF_4')) | r1_tsep_1(B_112, C_113) | ~m1_pre_topc(C_113, '#skF_1') | v2_struct_0(C_113) | ~m1_pre_topc(B_112, '#skF_1') | v2_struct_0(B_112))), inference(negUnitSimplification, [status(thm)], [c_42, c_318])).
% 2.86/1.40  tff(c_330, plain, (![B_114, C_115]: (m1_pre_topc(k2_tsep_1('#skF_1', B_114, C_115), '#skF_4') | r1_tsep_1(B_114, C_115) | ~m1_pre_topc(C_115, '#skF_1') | v2_struct_0(C_115) | v2_struct_0(B_114) | ~m1_pre_topc(B_114, '#skF_4') | ~m1_pre_topc(B_114, '#skF_1'))), inference(resolution, [status(thm)], [c_63, c_320])).
% 2.86/1.40  tff(c_18, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.86/1.40  tff(c_337, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_330, c_18])).
% 2.86/1.40  tff(c_342, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_24, c_30, c_337])).
% 2.86/1.40  tff(c_344, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_32, c_20, c_342])).
% 2.86/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.40  
% 2.86/1.40  Inference rules
% 2.86/1.40  ----------------------
% 2.86/1.40  #Ref     : 0
% 2.86/1.40  #Sup     : 81
% 2.86/1.40  #Fact    : 0
% 2.86/1.40  #Define  : 0
% 2.86/1.40  #Split   : 3
% 2.86/1.40  #Chain   : 0
% 2.86/1.40  #Close   : 0
% 2.86/1.40  
% 2.86/1.40  Ordering : KBO
% 2.86/1.40  
% 2.86/1.40  Simplification rules
% 2.86/1.40  ----------------------
% 2.86/1.40  #Subsume      : 13
% 2.86/1.40  #Demod        : 18
% 2.86/1.40  #Tautology    : 8
% 2.86/1.40  #SimpNegUnit  : 6
% 2.86/1.40  #BackRed      : 0
% 2.86/1.40  
% 2.86/1.40  #Partial instantiations: 0
% 2.86/1.40  #Strategies tried      : 1
% 2.86/1.40  
% 2.86/1.40  Timing (in seconds)
% 2.86/1.40  ----------------------
% 2.86/1.41  Preprocessing        : 0.31
% 2.86/1.41  Parsing              : 0.17
% 2.86/1.41  CNF conversion       : 0.03
% 2.86/1.41  Main loop            : 0.35
% 2.86/1.41  Inferencing          : 0.14
% 2.86/1.41  Reduction            : 0.08
% 2.86/1.41  Demodulation         : 0.06
% 2.86/1.41  BG Simplification    : 0.02
% 2.86/1.41  Subsumption          : 0.09
% 2.86/1.41  Abstraction          : 0.02
% 2.86/1.41  MUC search           : 0.00
% 2.86/1.41  Cooper               : 0.00
% 2.86/1.41  Total                : 0.69
% 2.86/1.41  Index Insertion      : 0.00
% 2.86/1.41  Index Deletion       : 0.00
% 2.86/1.41  Index Matching       : 0.00
% 2.86/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------

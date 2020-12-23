%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:55 EST 2020

% Result     : Theorem 11.20s
% Output     : CNFRefutation 11.32s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 105 expanded)
%              Number of leaves         :   29 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :  138 ( 326 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_111,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_compts_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v4_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v4_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k3_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tops_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_92,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_compts_1)).

tff(c_8,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_74,plain,(
    ! [A_40,B_41] : k1_setfam_1(k2_tarski(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_170,plain,(
    ! [A_49,B_50] : k1_setfam_1(k2_tarski(A_49,B_50)) = k3_xboole_0(B_50,A_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_74])).

tff(c_12,plain,(
    ! [A_13,B_14] : k1_setfam_1(k2_tarski(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_176,plain,(
    ! [B_50,A_49] : k3_xboole_0(B_50,A_49) = k3_xboole_0(A_49,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_12])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_238,plain,(
    ! [A_53,B_54,C_55] :
      ( k9_subset_1(A_53,B_54,C_55) = k3_xboole_0(B_54,C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_247,plain,(
    ! [B_54] : k9_subset_1(u1_struct_0('#skF_1'),B_54,'#skF_3') = k3_xboole_0(B_54,'#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_238])).

tff(c_24,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_288,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_24])).

tff(c_289,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_288])).

tff(c_94,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | ~ m1_subset_1(A_44,k1_zfmisc_1(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_106,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_94])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_26,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_30,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_419,plain,(
    ! [B_64,A_65] :
      ( v4_pre_topc(B_64,A_65)
      | ~ v2_compts_1(B_64,A_65)
      | ~ v8_pre_topc(A_65)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_429,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_419])).

tff(c_436,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_30,c_26,c_429])).

tff(c_28,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_426,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_419])).

tff(c_433,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_30,c_28,c_426])).

tff(c_497,plain,(
    ! [B_68,C_69,A_70] :
      ( v4_pre_topc(k3_xboole_0(B_68,C_69),A_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ v4_pre_topc(C_69,A_70)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ v4_pre_topc(B_68,A_70)
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_502,plain,(
    ! [B_68] :
      ( v4_pre_topc(k3_xboole_0(B_68,'#skF_2'),'#skF_1')
      | ~ v4_pre_topc('#skF_2','#skF_1')
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v4_pre_topc(B_68,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_497])).

tff(c_751,plain,(
    ! [B_78] :
      ( v4_pre_topc(k3_xboole_0(B_78,'#skF_2'),'#skF_1')
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v4_pre_topc(B_78,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_433,c_502])).

tff(c_761,plain,
    ( v4_pre_topc(k3_xboole_0('#skF_3','#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_751])).

tff(c_768,plain,(
    v4_pre_topc(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_761])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(k3_xboole_0(A_1,C_3),B_2)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(k3_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_666,plain,(
    ! [C_73,A_74,B_75] :
      ( v2_compts_1(C_73,A_74)
      | ~ v4_pre_topc(C_73,A_74)
      | ~ r1_tarski(C_73,B_75)
      | ~ v2_compts_1(B_75,A_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1994,plain,(
    ! [A_113,B_114,A_115] :
      ( v2_compts_1(k3_xboole_0(A_113,B_114),A_115)
      | ~ v4_pre_topc(k3_xboole_0(A_113,B_114),A_115)
      | ~ v2_compts_1(A_113,A_115)
      | ~ m1_subset_1(k3_xboole_0(A_113,B_114),k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ m1_subset_1(A_113,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115)
      | ~ v2_pre_topc(A_115) ) ),
    inference(resolution,[status(thm)],[c_4,c_666])).

tff(c_6452,plain,(
    ! [A_190,B_191,A_192] :
      ( v2_compts_1(k3_xboole_0(A_190,B_191),A_192)
      | ~ v4_pre_topc(k3_xboole_0(A_190,B_191),A_192)
      | ~ v2_compts_1(A_190,A_192)
      | ~ m1_subset_1(A_190,k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ l1_pre_topc(A_192)
      | ~ v2_pre_topc(A_192)
      | ~ r1_tarski(k3_xboole_0(A_190,B_191),u1_struct_0(A_192)) ) ),
    inference(resolution,[status(thm)],[c_16,c_1994])).

tff(c_21678,plain,(
    ! [A_364,C_365,A_366] :
      ( v2_compts_1(k3_xboole_0(A_364,C_365),A_366)
      | ~ v4_pre_topc(k3_xboole_0(A_364,C_365),A_366)
      | ~ v2_compts_1(A_364,A_366)
      | ~ m1_subset_1(A_364,k1_zfmisc_1(u1_struct_0(A_366)))
      | ~ l1_pre_topc(A_366)
      | ~ v2_pre_topc(A_366)
      | ~ r1_tarski(A_364,u1_struct_0(A_366)) ) ),
    inference(resolution,[status(thm)],[c_2,c_6452])).

tff(c_21754,plain,
    ( v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_768,c_21678])).

tff(c_21822,plain,(
    v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_38,c_36,c_32,c_26,c_21754])).

tff(c_21824,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_289,c_21822])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:41:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.20/4.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.20/4.51  
% 11.20/4.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.20/4.51  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 11.20/4.51  
% 11.20/4.51  %Foreground sorts:
% 11.20/4.51  
% 11.20/4.51  
% 11.20/4.51  %Background operators:
% 11.20/4.51  
% 11.20/4.51  
% 11.20/4.51  %Foreground operators:
% 11.20/4.51  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 11.20/4.51  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 11.20/4.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.20/4.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.20/4.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.20/4.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.20/4.51  tff('#skF_2', type, '#skF_2': $i).
% 11.20/4.51  tff('#skF_3', type, '#skF_3': $i).
% 11.20/4.51  tff('#skF_1', type, '#skF_1': $i).
% 11.20/4.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.20/4.51  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 11.20/4.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.20/4.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.20/4.51  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.20/4.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.20/4.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.20/4.51  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 11.20/4.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.20/4.51  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.20/4.51  
% 11.32/4.53  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 11.32/4.53  tff(f_43, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 11.32/4.53  tff(f_111, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_compts_1)).
% 11.32/4.53  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 11.32/4.53  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.32/4.53  tff(f_74, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_compts_1)).
% 11.32/4.53  tff(f_61, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v4_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v4_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k3_xboole_0(B, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_tops_1)).
% 11.32/4.53  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 11.32/4.53  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 11.32/4.53  tff(f_92, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_compts_1)).
% 11.32/4.53  tff(c_8, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.32/4.53  tff(c_74, plain, (![A_40, B_41]: (k1_setfam_1(k2_tarski(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.32/4.53  tff(c_170, plain, (![A_49, B_50]: (k1_setfam_1(k2_tarski(A_49, B_50))=k3_xboole_0(B_50, A_49))), inference(superposition, [status(thm), theory('equality')], [c_8, c_74])).
% 11.32/4.53  tff(c_12, plain, (![A_13, B_14]: (k1_setfam_1(k2_tarski(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.32/4.53  tff(c_176, plain, (![B_50, A_49]: (k3_xboole_0(B_50, A_49)=k3_xboole_0(A_49, B_50))), inference(superposition, [status(thm), theory('equality')], [c_170, c_12])).
% 11.32/4.53  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 11.32/4.53  tff(c_238, plain, (![A_53, B_54, C_55]: (k9_subset_1(A_53, B_54, C_55)=k3_xboole_0(B_54, C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.32/4.53  tff(c_247, plain, (![B_54]: (k9_subset_1(u1_struct_0('#skF_1'), B_54, '#skF_3')=k3_xboole_0(B_54, '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_238])).
% 11.32/4.53  tff(c_24, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 11.32/4.53  tff(c_288, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_247, c_24])).
% 11.32/4.53  tff(c_289, plain, (~v2_compts_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_176, c_288])).
% 11.32/4.53  tff(c_94, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | ~m1_subset_1(A_44, k1_zfmisc_1(B_45)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.32/4.53  tff(c_106, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_94])).
% 11.32/4.53  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 11.32/4.53  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 11.32/4.53  tff(c_26, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 11.32/4.53  tff(c_30, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 11.32/4.53  tff(c_419, plain, (![B_64, A_65]: (v4_pre_topc(B_64, A_65) | ~v2_compts_1(B_64, A_65) | ~v8_pre_topc(A_65) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.32/4.53  tff(c_429, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_419])).
% 11.32/4.53  tff(c_436, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_30, c_26, c_429])).
% 11.32/4.53  tff(c_28, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 11.32/4.53  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 11.32/4.53  tff(c_426, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_419])).
% 11.32/4.53  tff(c_433, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_30, c_28, c_426])).
% 11.32/4.53  tff(c_497, plain, (![B_68, C_69, A_70]: (v4_pre_topc(k3_xboole_0(B_68, C_69), A_70) | ~m1_subset_1(C_69, k1_zfmisc_1(u1_struct_0(A_70))) | ~v4_pre_topc(C_69, A_70) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_70))) | ~v4_pre_topc(B_68, A_70) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.32/4.53  tff(c_502, plain, (![B_68]: (v4_pre_topc(k3_xboole_0(B_68, '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v4_pre_topc(B_68, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_497])).
% 11.32/4.53  tff(c_751, plain, (![B_78]: (v4_pre_topc(k3_xboole_0(B_78, '#skF_2'), '#skF_1') | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v4_pre_topc(B_78, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_433, c_502])).
% 11.32/4.53  tff(c_761, plain, (v4_pre_topc(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_751])).
% 11.32/4.53  tff(c_768, plain, (v4_pre_topc(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_436, c_761])).
% 11.32/4.53  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(k3_xboole_0(A_1, C_3), B_2) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.32/4.53  tff(c_16, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.32/4.53  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k3_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.32/4.53  tff(c_666, plain, (![C_73, A_74, B_75]: (v2_compts_1(C_73, A_74) | ~v4_pre_topc(C_73, A_74) | ~r1_tarski(C_73, B_75) | ~v2_compts_1(B_75, A_74) | ~m1_subset_1(C_73, k1_zfmisc_1(u1_struct_0(A_74))) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.32/4.53  tff(c_1994, plain, (![A_113, B_114, A_115]: (v2_compts_1(k3_xboole_0(A_113, B_114), A_115) | ~v4_pre_topc(k3_xboole_0(A_113, B_114), A_115) | ~v2_compts_1(A_113, A_115) | ~m1_subset_1(k3_xboole_0(A_113, B_114), k1_zfmisc_1(u1_struct_0(A_115))) | ~m1_subset_1(A_113, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115) | ~v2_pre_topc(A_115))), inference(resolution, [status(thm)], [c_4, c_666])).
% 11.32/4.53  tff(c_6452, plain, (![A_190, B_191, A_192]: (v2_compts_1(k3_xboole_0(A_190, B_191), A_192) | ~v4_pre_topc(k3_xboole_0(A_190, B_191), A_192) | ~v2_compts_1(A_190, A_192) | ~m1_subset_1(A_190, k1_zfmisc_1(u1_struct_0(A_192))) | ~l1_pre_topc(A_192) | ~v2_pre_topc(A_192) | ~r1_tarski(k3_xboole_0(A_190, B_191), u1_struct_0(A_192)))), inference(resolution, [status(thm)], [c_16, c_1994])).
% 11.32/4.53  tff(c_21678, plain, (![A_364, C_365, A_366]: (v2_compts_1(k3_xboole_0(A_364, C_365), A_366) | ~v4_pre_topc(k3_xboole_0(A_364, C_365), A_366) | ~v2_compts_1(A_364, A_366) | ~m1_subset_1(A_364, k1_zfmisc_1(u1_struct_0(A_366))) | ~l1_pre_topc(A_366) | ~v2_pre_topc(A_366) | ~r1_tarski(A_364, u1_struct_0(A_366)))), inference(resolution, [status(thm)], [c_2, c_6452])).
% 11.32/4.53  tff(c_21754, plain, (v2_compts_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_768, c_21678])).
% 11.32/4.53  tff(c_21822, plain, (v2_compts_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_38, c_36, c_32, c_26, c_21754])).
% 11.32/4.53  tff(c_21824, plain, $false, inference(negUnitSimplification, [status(thm)], [c_289, c_21822])).
% 11.32/4.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.32/4.53  
% 11.32/4.53  Inference rules
% 11.32/4.53  ----------------------
% 11.32/4.53  #Ref     : 0
% 11.32/4.53  #Sup     : 5532
% 11.32/4.53  #Fact    : 0
% 11.32/4.53  #Define  : 0
% 11.32/4.53  #Split   : 0
% 11.32/4.53  #Chain   : 0
% 11.32/4.53  #Close   : 0
% 11.32/4.53  
% 11.32/4.53  Ordering : KBO
% 11.32/4.53  
% 11.32/4.53  Simplification rules
% 11.32/4.53  ----------------------
% 11.32/4.53  #Subsume      : 731
% 11.32/4.53  #Demod        : 5646
% 11.32/4.53  #Tautology    : 2390
% 11.32/4.53  #SimpNegUnit  : 2
% 11.32/4.53  #BackRed      : 1
% 11.32/4.53  
% 11.32/4.53  #Partial instantiations: 0
% 11.32/4.53  #Strategies tried      : 1
% 11.32/4.53  
% 11.32/4.53  Timing (in seconds)
% 11.32/4.53  ----------------------
% 11.32/4.53  Preprocessing        : 0.32
% 11.32/4.53  Parsing              : 0.17
% 11.32/4.53  CNF conversion       : 0.02
% 11.32/4.53  Main loop            : 3.45
% 11.32/4.53  Inferencing          : 0.64
% 11.32/4.53  Reduction            : 1.81
% 11.32/4.53  Demodulation         : 1.61
% 11.32/4.53  BG Simplification    : 0.09
% 11.32/4.53  Subsumption          : 0.75
% 11.32/4.53  Abstraction          : 0.13
% 11.32/4.53  MUC search           : 0.00
% 11.32/4.53  Cooper               : 0.00
% 11.32/4.53  Total                : 3.80
% 11.32/4.53  Index Insertion      : 0.00
% 11.32/4.53  Index Deletion       : 0.00
% 11.32/4.53  Index Matching       : 0.00
% 11.32/4.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------

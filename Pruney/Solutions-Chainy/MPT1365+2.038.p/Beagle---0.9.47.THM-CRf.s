%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:59 EST 2020

% Result     : Theorem 4.15s
% Output     : CNFRefutation 4.15s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 111 expanded)
%              Number of leaves         :   33 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :  138 ( 341 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_121,negated_conjecture,(
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

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & v4_pre_topc(C,A) )
               => v4_pre_topc(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_102,axiom,(
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

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_225,plain,(
    ! [A_105,B_106,C_107] :
      ( k9_subset_1(A_105,B_106,C_107) = k3_xboole_0(B_106,C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(A_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_234,plain,(
    ! [B_106] : k9_subset_1(u1_struct_0('#skF_1'),B_106,'#skF_3') = k3_xboole_0(B_106,'#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_225])).

tff(c_32,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_244,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_32])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_36,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_38,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_639,plain,(
    ! [B_182,A_183] :
      ( v4_pre_topc(B_182,A_183)
      | ~ v2_compts_1(B_182,A_183)
      | ~ v8_pre_topc(A_183)
      | ~ m1_subset_1(B_182,k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ l1_pre_topc(A_183)
      | ~ v2_pre_topc(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_646,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_639])).

tff(c_653,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_36,c_646])).

tff(c_34,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_649,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_639])).

tff(c_656,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_34,c_649])).

tff(c_1253,plain,(
    ! [A_263,B_264,C_265] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(A_263),B_264,C_265),A_263)
      | ~ v4_pre_topc(C_265,A_263)
      | ~ v4_pre_topc(B_264,A_263)
      | ~ m1_subset_1(C_265,k1_zfmisc_1(u1_struct_0(A_263)))
      | ~ m1_subset_1(B_264,k1_zfmisc_1(u1_struct_0(A_263)))
      | ~ l1_pre_topc(A_263)
      | ~ v2_pre_topc(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1276,plain,(
    ! [B_106] :
      ( v4_pre_topc(k3_xboole_0(B_106,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc('#skF_3','#skF_1')
      | ~ v4_pre_topc(B_106,'#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_1253])).

tff(c_1292,plain,(
    ! [B_266] :
      ( v4_pre_topc(k3_xboole_0(B_266,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(B_266,'#skF_1')
      | ~ m1_subset_1(B_266,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_656,c_1276])).

tff(c_1299,plain,
    ( v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1292])).

tff(c_1306,plain,(
    v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_1299])).

tff(c_67,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(A_69,B_70)
      | ~ m1_subset_1(A_69,k1_zfmisc_1(B_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_78,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_42,c_67])).

tff(c_80,plain,(
    ! [A_71,C_72,B_73] :
      ( r1_tarski(A_71,C_72)
      | ~ r1_tarski(B_73,C_72)
      | ~ r1_tarski(A_71,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_88,plain,(
    ! [A_71] :
      ( r1_tarski(A_71,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_71,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_78,c_80])).

tff(c_24,plain,(
    ! [A_38,B_39] :
      ( m1_subset_1(A_38,k1_zfmisc_1(B_39))
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1016,plain,(
    ! [C_227,A_228,B_229] :
      ( v2_compts_1(C_227,A_228)
      | ~ v4_pre_topc(C_227,A_228)
      | ~ r1_tarski(C_227,B_229)
      | ~ v2_compts_1(B_229,A_228)
      | ~ m1_subset_1(C_227,k1_zfmisc_1(u1_struct_0(A_228)))
      | ~ m1_subset_1(B_229,k1_zfmisc_1(u1_struct_0(A_228)))
      | ~ l1_pre_topc(A_228)
      | ~ v2_pre_topc(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1335,plain,(
    ! [A_271,B_272,A_273] :
      ( v2_compts_1(k3_xboole_0(A_271,B_272),A_273)
      | ~ v4_pre_topc(k3_xboole_0(A_271,B_272),A_273)
      | ~ v2_compts_1(A_271,A_273)
      | ~ m1_subset_1(k3_xboole_0(A_271,B_272),k1_zfmisc_1(u1_struct_0(A_273)))
      | ~ m1_subset_1(A_271,k1_zfmisc_1(u1_struct_0(A_273)))
      | ~ l1_pre_topc(A_273)
      | ~ v2_pre_topc(A_273) ) ),
    inference(resolution,[status(thm)],[c_2,c_1016])).

tff(c_1707,plain,(
    ! [A_320,B_321,A_322] :
      ( v2_compts_1(k3_xboole_0(A_320,B_321),A_322)
      | ~ v4_pre_topc(k3_xboole_0(A_320,B_321),A_322)
      | ~ v2_compts_1(A_320,A_322)
      | ~ m1_subset_1(A_320,k1_zfmisc_1(u1_struct_0(A_322)))
      | ~ l1_pre_topc(A_322)
      | ~ v2_pre_topc(A_322)
      | ~ r1_tarski(k3_xboole_0(A_320,B_321),u1_struct_0(A_322)) ) ),
    inference(resolution,[status(thm)],[c_24,c_1335])).

tff(c_1765,plain,(
    ! [A_320,B_321] :
      ( v2_compts_1(k3_xboole_0(A_320,B_321),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(A_320,B_321),'#skF_1')
      | ~ v2_compts_1(A_320,'#skF_1')
      | ~ m1_subset_1(A_320,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(k3_xboole_0(A_320,B_321),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_88,c_1707])).

tff(c_2005,plain,(
    ! [A_353,B_354] :
      ( v2_compts_1(k3_xboole_0(A_353,B_354),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(A_353,B_354),'#skF_1')
      | ~ v2_compts_1(A_353,'#skF_1')
      | ~ m1_subset_1(A_353,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(k3_xboole_0(A_353,B_354),'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1765])).

tff(c_2025,plain,
    ( v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1306,c_2005])).

tff(c_2058,plain,(
    v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_42,c_36,c_2025])).

tff(c_2060,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_244,c_2058])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:05:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.15/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.15/1.73  
% 4.15/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.15/1.73  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 4.15/1.73  
% 4.15/1.73  %Foreground sorts:
% 4.15/1.73  
% 4.15/1.73  
% 4.15/1.73  %Background operators:
% 4.15/1.73  
% 4.15/1.73  
% 4.15/1.73  %Foreground operators:
% 4.15/1.73  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 4.15/1.73  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 4.15/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.15/1.73  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.15/1.73  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.15/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.15/1.73  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.15/1.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.15/1.73  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.15/1.73  tff('#skF_2', type, '#skF_2': $i).
% 4.15/1.73  tff('#skF_3', type, '#skF_3': $i).
% 4.15/1.73  tff('#skF_1', type, '#skF_1': $i).
% 4.15/1.73  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.15/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.15/1.73  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.15/1.73  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.15/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.15/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.15/1.73  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.15/1.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.15/1.73  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.15/1.73  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.15/1.73  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.15/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.15/1.73  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.15/1.73  
% 4.15/1.74  tff(f_121, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_compts_1)).
% 4.15/1.74  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.15/1.74  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.15/1.74  tff(f_84, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_compts_1)).
% 4.15/1.74  tff(f_71, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => v4_pre_topc(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tops_1)).
% 4.15/1.74  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.15/1.74  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.15/1.74  tff(f_102, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_compts_1)).
% 4.15/1.74  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.15/1.74  tff(c_225, plain, (![A_105, B_106, C_107]: (k9_subset_1(A_105, B_106, C_107)=k3_xboole_0(B_106, C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(A_105)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.15/1.74  tff(c_234, plain, (![B_106]: (k9_subset_1(u1_struct_0('#skF_1'), B_106, '#skF_3')=k3_xboole_0(B_106, '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_225])).
% 4.15/1.74  tff(c_32, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.15/1.74  tff(c_244, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_234, c_32])).
% 4.15/1.74  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.15/1.74  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.15/1.74  tff(c_36, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.15/1.74  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.15/1.74  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.15/1.74  tff(c_38, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.15/1.74  tff(c_639, plain, (![B_182, A_183]: (v4_pre_topc(B_182, A_183) | ~v2_compts_1(B_182, A_183) | ~v8_pre_topc(A_183) | ~m1_subset_1(B_182, k1_zfmisc_1(u1_struct_0(A_183))) | ~l1_pre_topc(A_183) | ~v2_pre_topc(A_183))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.15/1.74  tff(c_646, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_639])).
% 4.15/1.74  tff(c_653, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_36, c_646])).
% 4.15/1.74  tff(c_34, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.15/1.74  tff(c_649, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_639])).
% 4.15/1.74  tff(c_656, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_34, c_649])).
% 4.15/1.74  tff(c_1253, plain, (![A_263, B_264, C_265]: (v4_pre_topc(k9_subset_1(u1_struct_0(A_263), B_264, C_265), A_263) | ~v4_pre_topc(C_265, A_263) | ~v4_pre_topc(B_264, A_263) | ~m1_subset_1(C_265, k1_zfmisc_1(u1_struct_0(A_263))) | ~m1_subset_1(B_264, k1_zfmisc_1(u1_struct_0(A_263))) | ~l1_pre_topc(A_263) | ~v2_pre_topc(A_263))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.15/1.74  tff(c_1276, plain, (![B_106]: (v4_pre_topc(k3_xboole_0(B_106, '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1') | ~v4_pre_topc(B_106, '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_234, c_1253])).
% 4.15/1.74  tff(c_1292, plain, (![B_266]: (v4_pre_topc(k3_xboole_0(B_266, '#skF_3'), '#skF_1') | ~v4_pre_topc(B_266, '#skF_1') | ~m1_subset_1(B_266, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_40, c_656, c_1276])).
% 4.15/1.74  tff(c_1299, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_1292])).
% 4.15/1.74  tff(c_1306, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_653, c_1299])).
% 4.15/1.74  tff(c_67, plain, (![A_69, B_70]: (r1_tarski(A_69, B_70) | ~m1_subset_1(A_69, k1_zfmisc_1(B_70)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.15/1.74  tff(c_78, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_67])).
% 4.15/1.74  tff(c_80, plain, (![A_71, C_72, B_73]: (r1_tarski(A_71, C_72) | ~r1_tarski(B_73, C_72) | ~r1_tarski(A_71, B_73))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.15/1.74  tff(c_88, plain, (![A_71]: (r1_tarski(A_71, u1_struct_0('#skF_1')) | ~r1_tarski(A_71, '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_80])).
% 4.15/1.74  tff(c_24, plain, (![A_38, B_39]: (m1_subset_1(A_38, k1_zfmisc_1(B_39)) | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.15/1.74  tff(c_1016, plain, (![C_227, A_228, B_229]: (v2_compts_1(C_227, A_228) | ~v4_pre_topc(C_227, A_228) | ~r1_tarski(C_227, B_229) | ~v2_compts_1(B_229, A_228) | ~m1_subset_1(C_227, k1_zfmisc_1(u1_struct_0(A_228))) | ~m1_subset_1(B_229, k1_zfmisc_1(u1_struct_0(A_228))) | ~l1_pre_topc(A_228) | ~v2_pre_topc(A_228))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.15/1.74  tff(c_1335, plain, (![A_271, B_272, A_273]: (v2_compts_1(k3_xboole_0(A_271, B_272), A_273) | ~v4_pre_topc(k3_xboole_0(A_271, B_272), A_273) | ~v2_compts_1(A_271, A_273) | ~m1_subset_1(k3_xboole_0(A_271, B_272), k1_zfmisc_1(u1_struct_0(A_273))) | ~m1_subset_1(A_271, k1_zfmisc_1(u1_struct_0(A_273))) | ~l1_pre_topc(A_273) | ~v2_pre_topc(A_273))), inference(resolution, [status(thm)], [c_2, c_1016])).
% 4.15/1.74  tff(c_1707, plain, (![A_320, B_321, A_322]: (v2_compts_1(k3_xboole_0(A_320, B_321), A_322) | ~v4_pre_topc(k3_xboole_0(A_320, B_321), A_322) | ~v2_compts_1(A_320, A_322) | ~m1_subset_1(A_320, k1_zfmisc_1(u1_struct_0(A_322))) | ~l1_pre_topc(A_322) | ~v2_pre_topc(A_322) | ~r1_tarski(k3_xboole_0(A_320, B_321), u1_struct_0(A_322)))), inference(resolution, [status(thm)], [c_24, c_1335])).
% 4.15/1.74  tff(c_1765, plain, (![A_320, B_321]: (v2_compts_1(k3_xboole_0(A_320, B_321), '#skF_1') | ~v4_pre_topc(k3_xboole_0(A_320, B_321), '#skF_1') | ~v2_compts_1(A_320, '#skF_1') | ~m1_subset_1(A_320, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(k3_xboole_0(A_320, B_321), '#skF_2'))), inference(resolution, [status(thm)], [c_88, c_1707])).
% 4.15/1.74  tff(c_2005, plain, (![A_353, B_354]: (v2_compts_1(k3_xboole_0(A_353, B_354), '#skF_1') | ~v4_pre_topc(k3_xboole_0(A_353, B_354), '#skF_1') | ~v2_compts_1(A_353, '#skF_1') | ~m1_subset_1(A_353, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(k3_xboole_0(A_353, B_354), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1765])).
% 4.15/1.74  tff(c_2025, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_1306, c_2005])).
% 4.15/1.74  tff(c_2058, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_42, c_36, c_2025])).
% 4.15/1.74  tff(c_2060, plain, $false, inference(negUnitSimplification, [status(thm)], [c_244, c_2058])).
% 4.15/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.15/1.74  
% 4.15/1.74  Inference rules
% 4.15/1.74  ----------------------
% 4.15/1.74  #Ref     : 0
% 4.15/1.74  #Sup     : 437
% 4.15/1.74  #Fact    : 0
% 4.15/1.74  #Define  : 0
% 4.15/1.74  #Split   : 0
% 4.15/1.74  #Chain   : 0
% 4.15/1.74  #Close   : 0
% 4.15/1.74  
% 4.15/1.74  Ordering : KBO
% 4.15/1.74  
% 4.15/1.74  Simplification rules
% 4.15/1.74  ----------------------
% 4.15/1.74  #Subsume      : 56
% 4.15/1.74  #Demod        : 191
% 4.15/1.74  #Tautology    : 146
% 4.15/1.74  #SimpNegUnit  : 1
% 4.15/1.74  #BackRed      : 1
% 4.15/1.74  
% 4.15/1.74  #Partial instantiations: 0
% 4.15/1.74  #Strategies tried      : 1
% 4.15/1.74  
% 4.15/1.74  Timing (in seconds)
% 4.15/1.74  ----------------------
% 4.15/1.74  Preprocessing        : 0.33
% 4.15/1.74  Parsing              : 0.18
% 4.15/1.74  CNF conversion       : 0.02
% 4.15/1.74  Main loop            : 0.64
% 4.15/1.74  Inferencing          : 0.25
% 4.15/1.74  Reduction            : 0.18
% 4.15/1.74  Demodulation         : 0.13
% 4.15/1.74  BG Simplification    : 0.03
% 4.15/1.74  Subsumption          : 0.13
% 4.15/1.74  Abstraction          : 0.04
% 4.15/1.74  MUC search           : 0.00
% 4.15/1.74  Cooper               : 0.00
% 4.15/1.75  Total                : 1.00
% 4.15/1.75  Index Insertion      : 0.00
% 4.15/1.75  Index Deletion       : 0.00
% 4.15/1.75  Index Matching       : 0.00
% 4.15/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------

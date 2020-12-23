%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:13 EST 2020

% Result     : Theorem 14.41s
% Output     : CNFRefutation 14.41s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 184 expanded)
%              Number of leaves         :   31 (  78 expanded)
%              Depth                    :   10
%              Number of atoms          :  122 ( 419 expanded)
%              Number of equality atoms :    8 (  31 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v2_tex_2(B,A)
                    | v2_tex_2(C,A) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_34,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2244,plain,(
    ! [A_303,B_304] :
      ( ~ r2_hidden('#skF_1'(A_303,B_304),B_304)
      | r1_tarski(A_303,B_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2249,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_2244])).

tff(c_32,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(A_46,k1_zfmisc_1(B_47))
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_282,plain,(
    ! [A_117,B_118,C_119] :
      ( k9_subset_1(A_117,B_118,C_119) = k3_xboole_0(B_118,C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(A_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_293,plain,(
    ! [B_118] : k9_subset_1(u1_struct_0('#skF_2'),B_118,'#skF_4') = k3_xboole_0(B_118,'#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_282])).

tff(c_36,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_295,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_36])).

tff(c_38,plain,
    ( v2_tex_2('#skF_4','#skF_2')
    | v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_46,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_296,plain,(
    ! [B_120] : k9_subset_1(u1_struct_0('#skF_2'),B_120,'#skF_4') = k3_xboole_0(B_120,'#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_282])).

tff(c_24,plain,(
    ! [A_38,B_39,C_40] :
      ( m1_subset_1(k9_subset_1(A_38,B_39,C_40),k1_zfmisc_1(A_38))
      | ~ m1_subset_1(C_40,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_305,plain,(
    ! [B_120] :
      ( m1_subset_1(k3_xboole_0(B_120,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_24])).

tff(c_313,plain,(
    ! [B_120] : m1_subset_1(k3_xboole_0(B_120,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_305])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_959,plain,(
    ! [C_198,A_199,B_200] :
      ( v2_tex_2(C_198,A_199)
      | ~ v2_tex_2(B_200,A_199)
      | ~ r1_tarski(C_198,B_200)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(u1_struct_0(A_199)))
      | ~ m1_subset_1(B_200,k1_zfmisc_1(u1_struct_0(A_199)))
      | ~ l1_pre_topc(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1474,plain,(
    ! [A_249,B_250,A_251] :
      ( v2_tex_2(k3_xboole_0(A_249,B_250),A_251)
      | ~ v2_tex_2(A_249,A_251)
      | ~ m1_subset_1(k3_xboole_0(A_249,B_250),k1_zfmisc_1(u1_struct_0(A_251)))
      | ~ m1_subset_1(A_249,k1_zfmisc_1(u1_struct_0(A_251)))
      | ~ l1_pre_topc(A_251) ) ),
    inference(resolution,[status(thm)],[c_8,c_959])).

tff(c_1490,plain,(
    ! [B_120] :
      ( v2_tex_2(k3_xboole_0(B_120,'#skF_4'),'#skF_2')
      | ~ v2_tex_2(B_120,'#skF_2')
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_313,c_1474])).

tff(c_2165,plain,(
    ! [B_292] :
      ( v2_tex_2(k3_xboole_0(B_292,'#skF_4'),'#skF_2')
      | ~ v2_tex_2(B_292,'#skF_2')
      | ~ m1_subset_1(B_292,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1490])).

tff(c_2195,plain,
    ( v2_tex_2(k3_xboole_0('#skF_3','#skF_4'),'#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_2165])).

tff(c_2206,plain,(
    v2_tex_2(k3_xboole_0('#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2195])).

tff(c_2208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_295,c_2206])).

tff(c_2209,plain,(
    v2_tex_2('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_2421,plain,(
    ! [A_343,B_344,C_345] :
      ( k9_subset_1(A_343,B_344,C_345) = k3_xboole_0(B_344,C_345)
      | ~ m1_subset_1(C_345,k1_zfmisc_1(A_343)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2429,plain,(
    ! [B_344] : k9_subset_1(u1_struct_0('#skF_2'),B_344,'#skF_4') = k3_xboole_0(B_344,'#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_2421])).

tff(c_2492,plain,(
    ! [A_353,B_354,C_355] :
      ( m1_subset_1(k9_subset_1(A_353,B_354,C_355),k1_zfmisc_1(A_353))
      | ~ m1_subset_1(C_355,k1_zfmisc_1(A_353)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2506,plain,(
    ! [B_344] :
      ( m1_subset_1(k3_xboole_0(B_344,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2429,c_2492])).

tff(c_2512,plain,(
    ! [B_344] : m1_subset_1(k3_xboole_0(B_344,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2506])).

tff(c_2450,plain,(
    ! [B_348,B_349,A_350] :
      ( k9_subset_1(B_348,B_349,A_350) = k3_xboole_0(B_349,A_350)
      | ~ r1_tarski(A_350,B_348) ) ),
    inference(resolution,[status(thm)],[c_32,c_2421])).

tff(c_2477,plain,(
    ! [A_1,B_349] : k9_subset_1(A_1,B_349,A_1) = k3_xboole_0(B_349,A_1) ),
    inference(resolution,[status(thm)],[c_2249,c_2450])).

tff(c_30,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2508,plain,(
    ! [A_353,B_354,C_355] :
      ( r1_tarski(k9_subset_1(A_353,B_354,C_355),A_353)
      | ~ m1_subset_1(C_355,k1_zfmisc_1(A_353)) ) ),
    inference(resolution,[status(thm)],[c_2492,c_30])).

tff(c_3182,plain,(
    ! [C_438,A_439,B_440] :
      ( v2_tex_2(C_438,A_439)
      | ~ v2_tex_2(B_440,A_439)
      | ~ r1_tarski(C_438,B_440)
      | ~ m1_subset_1(C_438,k1_zfmisc_1(u1_struct_0(A_439)))
      | ~ m1_subset_1(B_440,k1_zfmisc_1(u1_struct_0(A_439)))
      | ~ l1_pre_topc(A_439) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6264,plain,(
    ! [A_642,B_643,C_644,A_645] :
      ( v2_tex_2(k9_subset_1(A_642,B_643,C_644),A_645)
      | ~ v2_tex_2(A_642,A_645)
      | ~ m1_subset_1(k9_subset_1(A_642,B_643,C_644),k1_zfmisc_1(u1_struct_0(A_645)))
      | ~ m1_subset_1(A_642,k1_zfmisc_1(u1_struct_0(A_645)))
      | ~ l1_pre_topc(A_645)
      | ~ m1_subset_1(C_644,k1_zfmisc_1(A_642)) ) ),
    inference(resolution,[status(thm)],[c_2508,c_3182])).

tff(c_6295,plain,(
    ! [A_1,B_349,A_645] :
      ( v2_tex_2(k9_subset_1(A_1,B_349,A_1),A_645)
      | ~ v2_tex_2(A_1,A_645)
      | ~ m1_subset_1(k3_xboole_0(B_349,A_1),k1_zfmisc_1(u1_struct_0(A_645)))
      | ~ m1_subset_1(A_1,k1_zfmisc_1(u1_struct_0(A_645)))
      | ~ l1_pre_topc(A_645)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2477,c_6264])).

tff(c_34787,plain,(
    ! [B_1558,A_1559,A_1560] :
      ( v2_tex_2(k3_xboole_0(B_1558,A_1559),A_1560)
      | ~ v2_tex_2(A_1559,A_1560)
      | ~ m1_subset_1(k3_xboole_0(B_1558,A_1559),k1_zfmisc_1(u1_struct_0(A_1560)))
      | ~ m1_subset_1(A_1559,k1_zfmisc_1(u1_struct_0(A_1560)))
      | ~ l1_pre_topc(A_1560)
      | ~ m1_subset_1(A_1559,k1_zfmisc_1(A_1559)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2477,c_6295])).

tff(c_34820,plain,(
    ! [B_344] :
      ( v2_tex_2(k3_xboole_0(B_344,'#skF_4'),'#skF_2')
      | ~ v2_tex_2('#skF_4','#skF_2')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_2512,c_34787])).

tff(c_34857,plain,(
    ! [B_344] :
      ( v2_tex_2(k3_xboole_0(B_344,'#skF_4'),'#skF_2')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_2209,c_34820])).

tff(c_34862,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_34857])).

tff(c_34865,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_34862])).

tff(c_34869,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2249,c_34865])).

tff(c_34870,plain,(
    ! [B_344] : v2_tex_2(k3_xboole_0(B_344,'#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_34857])).

tff(c_2431,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2429,c_36])).

tff(c_34925,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34870,c_2431])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:22:01 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.41/7.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.41/7.89  
% 14.41/7.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.41/7.89  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 14.41/7.89  
% 14.41/7.89  %Foreground sorts:
% 14.41/7.89  
% 14.41/7.89  
% 14.41/7.89  %Background operators:
% 14.41/7.89  
% 14.41/7.89  
% 14.41/7.89  %Foreground operators:
% 14.41/7.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.41/7.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.41/7.89  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 14.41/7.89  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 14.41/7.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.41/7.89  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 14.41/7.89  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.41/7.89  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 14.41/7.89  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 14.41/7.89  tff('#skF_2', type, '#skF_2': $i).
% 14.41/7.89  tff('#skF_3', type, '#skF_3': $i).
% 14.41/7.89  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 14.41/7.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.41/7.89  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 14.41/7.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.41/7.89  tff('#skF_4', type, '#skF_4': $i).
% 14.41/7.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.41/7.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.41/7.89  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 14.41/7.89  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.41/7.89  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.41/7.89  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 14.41/7.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.41/7.89  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 14.41/7.89  
% 14.41/7.91  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 14.41/7.91  tff(f_66, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 14.41/7.91  tff(f_95, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tex_2)).
% 14.41/7.91  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 14.41/7.91  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 14.41/7.91  tff(f_34, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 14.41/7.91  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_tex_2)).
% 14.41/7.91  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.41/7.91  tff(c_2244, plain, (![A_303, B_304]: (~r2_hidden('#skF_1'(A_303, B_304), B_304) | r1_tarski(A_303, B_304))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.41/7.91  tff(c_2249, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_2244])).
% 14.41/7.91  tff(c_32, plain, (![A_46, B_47]: (m1_subset_1(A_46, k1_zfmisc_1(B_47)) | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_66])).
% 14.41/7.91  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 14.41/7.91  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 14.41/7.91  tff(c_282, plain, (![A_117, B_118, C_119]: (k9_subset_1(A_117, B_118, C_119)=k3_xboole_0(B_118, C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(A_117)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 14.41/7.91  tff(c_293, plain, (![B_118]: (k9_subset_1(u1_struct_0('#skF_2'), B_118, '#skF_4')=k3_xboole_0(B_118, '#skF_4'))), inference(resolution, [status(thm)], [c_40, c_282])).
% 14.41/7.91  tff(c_36, plain, (~v2_tex_2(k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 14.41/7.91  tff(c_295, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_293, c_36])).
% 14.41/7.91  tff(c_38, plain, (v2_tex_2('#skF_4', '#skF_2') | v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 14.41/7.91  tff(c_46, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_38])).
% 14.41/7.91  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 14.41/7.91  tff(c_296, plain, (![B_120]: (k9_subset_1(u1_struct_0('#skF_2'), B_120, '#skF_4')=k3_xboole_0(B_120, '#skF_4'))), inference(resolution, [status(thm)], [c_40, c_282])).
% 14.41/7.91  tff(c_24, plain, (![A_38, B_39, C_40]: (m1_subset_1(k9_subset_1(A_38, B_39, C_40), k1_zfmisc_1(A_38)) | ~m1_subset_1(C_40, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.41/7.91  tff(c_305, plain, (![B_120]: (m1_subset_1(k3_xboole_0(B_120, '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_296, c_24])).
% 14.41/7.91  tff(c_313, plain, (![B_120]: (m1_subset_1(k3_xboole_0(B_120, '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_305])).
% 14.41/7.91  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 14.41/7.91  tff(c_959, plain, (![C_198, A_199, B_200]: (v2_tex_2(C_198, A_199) | ~v2_tex_2(B_200, A_199) | ~r1_tarski(C_198, B_200) | ~m1_subset_1(C_198, k1_zfmisc_1(u1_struct_0(A_199))) | ~m1_subset_1(B_200, k1_zfmisc_1(u1_struct_0(A_199))) | ~l1_pre_topc(A_199))), inference(cnfTransformation, [status(thm)], [f_80])).
% 14.41/7.91  tff(c_1474, plain, (![A_249, B_250, A_251]: (v2_tex_2(k3_xboole_0(A_249, B_250), A_251) | ~v2_tex_2(A_249, A_251) | ~m1_subset_1(k3_xboole_0(A_249, B_250), k1_zfmisc_1(u1_struct_0(A_251))) | ~m1_subset_1(A_249, k1_zfmisc_1(u1_struct_0(A_251))) | ~l1_pre_topc(A_251))), inference(resolution, [status(thm)], [c_8, c_959])).
% 14.41/7.91  tff(c_1490, plain, (![B_120]: (v2_tex_2(k3_xboole_0(B_120, '#skF_4'), '#skF_2') | ~v2_tex_2(B_120, '#skF_2') | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_313, c_1474])).
% 14.41/7.91  tff(c_2165, plain, (![B_292]: (v2_tex_2(k3_xboole_0(B_292, '#skF_4'), '#skF_2') | ~v2_tex_2(B_292, '#skF_2') | ~m1_subset_1(B_292, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1490])).
% 14.41/7.91  tff(c_2195, plain, (v2_tex_2(k3_xboole_0('#skF_3', '#skF_4'), '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_2165])).
% 14.41/7.91  tff(c_2206, plain, (v2_tex_2(k3_xboole_0('#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2195])).
% 14.41/7.91  tff(c_2208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_295, c_2206])).
% 14.41/7.91  tff(c_2209, plain, (v2_tex_2('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_38])).
% 14.41/7.91  tff(c_2421, plain, (![A_343, B_344, C_345]: (k9_subset_1(A_343, B_344, C_345)=k3_xboole_0(B_344, C_345) | ~m1_subset_1(C_345, k1_zfmisc_1(A_343)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 14.41/7.91  tff(c_2429, plain, (![B_344]: (k9_subset_1(u1_struct_0('#skF_2'), B_344, '#skF_4')=k3_xboole_0(B_344, '#skF_4'))), inference(resolution, [status(thm)], [c_40, c_2421])).
% 14.41/7.91  tff(c_2492, plain, (![A_353, B_354, C_355]: (m1_subset_1(k9_subset_1(A_353, B_354, C_355), k1_zfmisc_1(A_353)) | ~m1_subset_1(C_355, k1_zfmisc_1(A_353)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.41/7.91  tff(c_2506, plain, (![B_344]: (m1_subset_1(k3_xboole_0(B_344, '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_2429, c_2492])).
% 14.41/7.91  tff(c_2512, plain, (![B_344]: (m1_subset_1(k3_xboole_0(B_344, '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2506])).
% 14.41/7.91  tff(c_2450, plain, (![B_348, B_349, A_350]: (k9_subset_1(B_348, B_349, A_350)=k3_xboole_0(B_349, A_350) | ~r1_tarski(A_350, B_348))), inference(resolution, [status(thm)], [c_32, c_2421])).
% 14.41/7.91  tff(c_2477, plain, (![A_1, B_349]: (k9_subset_1(A_1, B_349, A_1)=k3_xboole_0(B_349, A_1))), inference(resolution, [status(thm)], [c_2249, c_2450])).
% 14.41/7.91  tff(c_30, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~m1_subset_1(A_46, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 14.41/7.91  tff(c_2508, plain, (![A_353, B_354, C_355]: (r1_tarski(k9_subset_1(A_353, B_354, C_355), A_353) | ~m1_subset_1(C_355, k1_zfmisc_1(A_353)))), inference(resolution, [status(thm)], [c_2492, c_30])).
% 14.41/7.91  tff(c_3182, plain, (![C_438, A_439, B_440]: (v2_tex_2(C_438, A_439) | ~v2_tex_2(B_440, A_439) | ~r1_tarski(C_438, B_440) | ~m1_subset_1(C_438, k1_zfmisc_1(u1_struct_0(A_439))) | ~m1_subset_1(B_440, k1_zfmisc_1(u1_struct_0(A_439))) | ~l1_pre_topc(A_439))), inference(cnfTransformation, [status(thm)], [f_80])).
% 14.41/7.91  tff(c_6264, plain, (![A_642, B_643, C_644, A_645]: (v2_tex_2(k9_subset_1(A_642, B_643, C_644), A_645) | ~v2_tex_2(A_642, A_645) | ~m1_subset_1(k9_subset_1(A_642, B_643, C_644), k1_zfmisc_1(u1_struct_0(A_645))) | ~m1_subset_1(A_642, k1_zfmisc_1(u1_struct_0(A_645))) | ~l1_pre_topc(A_645) | ~m1_subset_1(C_644, k1_zfmisc_1(A_642)))), inference(resolution, [status(thm)], [c_2508, c_3182])).
% 14.41/7.91  tff(c_6295, plain, (![A_1, B_349, A_645]: (v2_tex_2(k9_subset_1(A_1, B_349, A_1), A_645) | ~v2_tex_2(A_1, A_645) | ~m1_subset_1(k3_xboole_0(B_349, A_1), k1_zfmisc_1(u1_struct_0(A_645))) | ~m1_subset_1(A_1, k1_zfmisc_1(u1_struct_0(A_645))) | ~l1_pre_topc(A_645) | ~m1_subset_1(A_1, k1_zfmisc_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2477, c_6264])).
% 14.41/7.91  tff(c_34787, plain, (![B_1558, A_1559, A_1560]: (v2_tex_2(k3_xboole_0(B_1558, A_1559), A_1560) | ~v2_tex_2(A_1559, A_1560) | ~m1_subset_1(k3_xboole_0(B_1558, A_1559), k1_zfmisc_1(u1_struct_0(A_1560))) | ~m1_subset_1(A_1559, k1_zfmisc_1(u1_struct_0(A_1560))) | ~l1_pre_topc(A_1560) | ~m1_subset_1(A_1559, k1_zfmisc_1(A_1559)))), inference(demodulation, [status(thm), theory('equality')], [c_2477, c_6295])).
% 14.41/7.91  tff(c_34820, plain, (![B_344]: (v2_tex_2(k3_xboole_0(B_344, '#skF_4'), '#skF_2') | ~v2_tex_2('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_2512, c_34787])).
% 14.41/7.91  tff(c_34857, plain, (![B_344]: (v2_tex_2(k3_xboole_0(B_344, '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_2209, c_34820])).
% 14.41/7.91  tff(c_34862, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_34857])).
% 14.41/7.91  tff(c_34865, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_34862])).
% 14.41/7.91  tff(c_34869, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2249, c_34865])).
% 14.41/7.91  tff(c_34870, plain, (![B_344]: (v2_tex_2(k3_xboole_0(B_344, '#skF_4'), '#skF_2'))), inference(splitRight, [status(thm)], [c_34857])).
% 14.41/7.91  tff(c_2431, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2429, c_36])).
% 14.41/7.91  tff(c_34925, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34870, c_2431])).
% 14.41/7.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.41/7.91  
% 14.41/7.91  Inference rules
% 14.41/7.91  ----------------------
% 14.41/7.91  #Ref     : 0
% 14.41/7.91  #Sup     : 8069
% 14.41/7.91  #Fact    : 0
% 14.41/7.91  #Define  : 0
% 14.41/7.91  #Split   : 5
% 14.41/7.91  #Chain   : 0
% 14.41/7.91  #Close   : 0
% 14.41/7.91  
% 14.41/7.91  Ordering : KBO
% 14.41/7.91  
% 14.41/7.91  Simplification rules
% 14.41/7.91  ----------------------
% 14.41/7.91  #Subsume      : 594
% 14.41/7.91  #Demod        : 1219
% 14.41/7.91  #Tautology    : 724
% 14.41/7.91  #SimpNegUnit  : 10
% 14.41/7.91  #BackRed      : 4
% 14.41/7.91  
% 14.41/7.91  #Partial instantiations: 0
% 14.41/7.91  #Strategies tried      : 1
% 14.41/7.91  
% 14.41/7.91  Timing (in seconds)
% 14.41/7.91  ----------------------
% 14.41/7.91  Preprocessing        : 0.33
% 14.41/7.91  Parsing              : 0.19
% 14.41/7.91  CNF conversion       : 0.02
% 14.41/7.91  Main loop            : 6.76
% 14.41/7.91  Inferencing          : 1.09
% 14.41/7.91  Reduction            : 2.36
% 14.41/7.91  Demodulation         : 1.98
% 14.41/7.91  BG Simplification    : 0.15
% 14.41/7.91  Subsumption          : 2.78
% 14.41/7.91  Abstraction          : 0.20
% 14.41/7.91  MUC search           : 0.00
% 14.41/7.91  Cooper               : 0.00
% 14.41/7.91  Total                : 7.13
% 14.41/7.91  Index Insertion      : 0.00
% 14.41/7.91  Index Deletion       : 0.00
% 14.41/7.91  Index Matching       : 0.00
% 14.41/7.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------

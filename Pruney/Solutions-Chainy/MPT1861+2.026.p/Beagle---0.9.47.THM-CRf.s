%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:13 EST 2020

% Result     : Theorem 5.23s
% Output     : CNFRefutation 5.63s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 162 expanded)
%              Number of leaves         :   24 (  66 expanded)
%              Depth                    :   10
%              Number of atoms          :  118 ( 384 expanded)
%              Number of equality atoms :    9 (  36 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

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

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v2_tex_2(B,A)
                    | v2_tex_2(C,A) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_97,plain,(
    ! [A_49,B_50,C_51] :
      ( k9_subset_1(A_49,B_50,C_51) = k3_xboole_0(B_50,C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_108,plain,(
    ! [B_50] : k9_subset_1(u1_struct_0('#skF_1'),B_50,'#skF_3') = k3_xboole_0(B_50,'#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_97])).

tff(c_24,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_110,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_24])).

tff(c_26,plain,
    ( v2_tex_2('#skF_3','#skF_1')
    | v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_36,plain,(
    v2_tex_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_111,plain,(
    ! [B_52] : k9_subset_1(u1_struct_0('#skF_1'),B_52,'#skF_3') = k3_xboole_0(B_52,'#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_97])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9] :
      ( m1_subset_1(k9_subset_1(A_7,B_8,C_9),k1_zfmisc_1(A_7))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_120,plain,(
    ! [B_52] :
      ( m1_subset_1(k3_xboole_0(B_52,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_12])).

tff(c_128,plain,(
    ! [B_52] : m1_subset_1(k3_xboole_0(B_52,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_120])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_130,plain,(
    ! [C_53,A_54,B_55] :
      ( v2_tex_2(C_53,A_54)
      | ~ v2_tex_2(B_55,A_54)
      | ~ r1_tarski(C_53,B_55)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_390,plain,(
    ! [A_90,B_91,A_92] :
      ( v2_tex_2(k3_xboole_0(A_90,B_91),A_92)
      | ~ v2_tex_2(A_90,A_92)
      | ~ m1_subset_1(k3_xboole_0(A_90,B_91),k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ m1_subset_1(A_90,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(resolution,[status(thm)],[c_8,c_130])).

tff(c_403,plain,(
    ! [B_52] :
      ( v2_tex_2(k3_xboole_0(B_52,'#skF_3'),'#skF_1')
      | ~ v2_tex_2(B_52,'#skF_1')
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_128,c_390])).

tff(c_455,plain,(
    ! [B_99] :
      ( v2_tex_2(k3_xboole_0(B_99,'#skF_3'),'#skF_1')
      | ~ v2_tex_2(B_99,'#skF_1')
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_403])).

tff(c_485,plain,
    ( v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v2_tex_2('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_455])).

tff(c_496,plain,(
    v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_485])).

tff(c_498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_496])).

tff(c_499,plain,(
    v2_tex_2('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_550,plain,(
    ! [A_110,B_111,C_112] :
      ( k9_subset_1(A_110,B_111,C_112) = k3_xboole_0(B_111,C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(A_110)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_558,plain,(
    ! [B_111] : k9_subset_1(u1_struct_0('#skF_1'),B_111,'#skF_3') = k3_xboole_0(B_111,'#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_550])).

tff(c_605,plain,(
    ! [A_122,B_123,C_124] :
      ( m1_subset_1(k9_subset_1(A_122,B_123,C_124),k1_zfmisc_1(A_122))
      | ~ m1_subset_1(C_124,k1_zfmisc_1(A_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_619,plain,(
    ! [B_111] :
      ( m1_subset_1(k3_xboole_0(B_111,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_605])).

tff(c_625,plain,(
    ! [B_111] : m1_subset_1(k3_xboole_0(B_111,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_619])).

tff(c_581,plain,(
    ! [B_117,B_118,A_119] :
      ( k9_subset_1(B_117,B_118,A_119) = k3_xboole_0(B_118,A_119)
      | ~ r1_tarski(A_119,B_117) ) ),
    inference(resolution,[status(thm)],[c_20,c_550])).

tff(c_595,plain,(
    ! [B_2,B_118] : k9_subset_1(B_2,B_118,B_2) = k3_xboole_0(B_118,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_581])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_621,plain,(
    ! [A_122,B_123,C_124] :
      ( r1_tarski(k9_subset_1(A_122,B_123,C_124),A_122)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(A_122)) ) ),
    inference(resolution,[status(thm)],[c_605,c_18])).

tff(c_707,plain,(
    ! [C_140,A_141,B_142] :
      ( v2_tex_2(C_140,A_141)
      | ~ v2_tex_2(B_142,A_141)
      | ~ r1_tarski(C_140,B_142)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1626,plain,(
    ! [A_262,B_263,C_264,A_265] :
      ( v2_tex_2(k9_subset_1(A_262,B_263,C_264),A_265)
      | ~ v2_tex_2(A_262,A_265)
      | ~ m1_subset_1(k9_subset_1(A_262,B_263,C_264),k1_zfmisc_1(u1_struct_0(A_265)))
      | ~ m1_subset_1(A_262,k1_zfmisc_1(u1_struct_0(A_265)))
      | ~ l1_pre_topc(A_265)
      | ~ m1_subset_1(C_264,k1_zfmisc_1(A_262)) ) ),
    inference(resolution,[status(thm)],[c_621,c_707])).

tff(c_1660,plain,(
    ! [B_2,B_118,A_265] :
      ( v2_tex_2(k9_subset_1(B_2,B_118,B_2),A_265)
      | ~ v2_tex_2(B_2,A_265)
      | ~ m1_subset_1(k3_xboole_0(B_118,B_2),k1_zfmisc_1(u1_struct_0(A_265)))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(u1_struct_0(A_265)))
      | ~ l1_pre_topc(A_265)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_595,c_1626])).

tff(c_3317,plain,(
    ! [B_446,B_447,A_448] :
      ( v2_tex_2(k3_xboole_0(B_446,B_447),A_448)
      | ~ v2_tex_2(B_447,A_448)
      | ~ m1_subset_1(k3_xboole_0(B_446,B_447),k1_zfmisc_1(u1_struct_0(A_448)))
      | ~ m1_subset_1(B_447,k1_zfmisc_1(u1_struct_0(A_448)))
      | ~ l1_pre_topc(A_448)
      | ~ m1_subset_1(B_447,k1_zfmisc_1(B_447)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_595,c_1660])).

tff(c_3356,plain,(
    ! [B_111] :
      ( v2_tex_2(k3_xboole_0(B_111,'#skF_3'),'#skF_1')
      | ~ v2_tex_2('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_625,c_3317])).

tff(c_3395,plain,(
    ! [B_111] :
      ( v2_tex_2(k3_xboole_0(B_111,'#skF_3'),'#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_499,c_3356])).

tff(c_3400,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3395])).

tff(c_3403,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_3400])).

tff(c_3407,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3403])).

tff(c_3408,plain,(
    ! [B_111] : v2_tex_2(k3_xboole_0(B_111,'#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_3395])).

tff(c_561,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_24])).

tff(c_3439,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3408,c_561])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:17:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.23/2.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.23/2.06  
% 5.23/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.63/2.07  %$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 5.63/2.07  
% 5.63/2.07  %Foreground sorts:
% 5.63/2.07  
% 5.63/2.07  
% 5.63/2.07  %Background operators:
% 5.63/2.07  
% 5.63/2.07  
% 5.63/2.07  %Foreground operators:
% 5.63/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.63/2.07  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.63/2.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.63/2.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.63/2.07  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 5.63/2.07  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.63/2.07  tff('#skF_2', type, '#skF_2': $i).
% 5.63/2.07  tff('#skF_3', type, '#skF_3': $i).
% 5.63/2.07  tff('#skF_1', type, '#skF_1': $i).
% 5.63/2.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.63/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.63/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.63/2.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.63/2.07  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.63/2.07  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.63/2.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.63/2.07  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.63/2.07  
% 5.63/2.08  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.63/2.08  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.63/2.08  tff(f_78, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tex_2)).
% 5.63/2.08  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 5.63/2.08  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 5.63/2.08  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.63/2.08  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_tex_2)).
% 5.63/2.08  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.63/2.08  tff(c_20, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.63/2.08  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.63/2.08  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.63/2.08  tff(c_97, plain, (![A_49, B_50, C_51]: (k9_subset_1(A_49, B_50, C_51)=k3_xboole_0(B_50, C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.63/2.08  tff(c_108, plain, (![B_50]: (k9_subset_1(u1_struct_0('#skF_1'), B_50, '#skF_3')=k3_xboole_0(B_50, '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_97])).
% 5.63/2.08  tff(c_24, plain, (~v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.63/2.08  tff(c_110, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_24])).
% 5.63/2.08  tff(c_26, plain, (v2_tex_2('#skF_3', '#skF_1') | v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.63/2.08  tff(c_36, plain, (v2_tex_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_26])).
% 5.63/2.08  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.63/2.08  tff(c_111, plain, (![B_52]: (k9_subset_1(u1_struct_0('#skF_1'), B_52, '#skF_3')=k3_xboole_0(B_52, '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_97])).
% 5.63/2.08  tff(c_12, plain, (![A_7, B_8, C_9]: (m1_subset_1(k9_subset_1(A_7, B_8, C_9), k1_zfmisc_1(A_7)) | ~m1_subset_1(C_9, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.63/2.08  tff(c_120, plain, (![B_52]: (m1_subset_1(k3_xboole_0(B_52, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_111, c_12])).
% 5.63/2.08  tff(c_128, plain, (![B_52]: (m1_subset_1(k3_xboole_0(B_52, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_120])).
% 5.63/2.08  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.63/2.08  tff(c_130, plain, (![C_53, A_54, B_55]: (v2_tex_2(C_53, A_54) | ~v2_tex_2(B_55, A_54) | ~r1_tarski(C_53, B_55) | ~m1_subset_1(C_53, k1_zfmisc_1(u1_struct_0(A_54))) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.63/2.08  tff(c_390, plain, (![A_90, B_91, A_92]: (v2_tex_2(k3_xboole_0(A_90, B_91), A_92) | ~v2_tex_2(A_90, A_92) | ~m1_subset_1(k3_xboole_0(A_90, B_91), k1_zfmisc_1(u1_struct_0(A_92))) | ~m1_subset_1(A_90, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(resolution, [status(thm)], [c_8, c_130])).
% 5.63/2.08  tff(c_403, plain, (![B_52]: (v2_tex_2(k3_xboole_0(B_52, '#skF_3'), '#skF_1') | ~v2_tex_2(B_52, '#skF_1') | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_128, c_390])).
% 5.63/2.08  tff(c_455, plain, (![B_99]: (v2_tex_2(k3_xboole_0(B_99, '#skF_3'), '#skF_1') | ~v2_tex_2(B_99, '#skF_1') | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_403])).
% 5.63/2.08  tff(c_485, plain, (v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v2_tex_2('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_455])).
% 5.63/2.08  tff(c_496, plain, (v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_485])).
% 5.63/2.08  tff(c_498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_496])).
% 5.63/2.08  tff(c_499, plain, (v2_tex_2('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_26])).
% 5.63/2.08  tff(c_550, plain, (![A_110, B_111, C_112]: (k9_subset_1(A_110, B_111, C_112)=k3_xboole_0(B_111, C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(A_110)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.63/2.08  tff(c_558, plain, (![B_111]: (k9_subset_1(u1_struct_0('#skF_1'), B_111, '#skF_3')=k3_xboole_0(B_111, '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_550])).
% 5.63/2.08  tff(c_605, plain, (![A_122, B_123, C_124]: (m1_subset_1(k9_subset_1(A_122, B_123, C_124), k1_zfmisc_1(A_122)) | ~m1_subset_1(C_124, k1_zfmisc_1(A_122)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.63/2.08  tff(c_619, plain, (![B_111]: (m1_subset_1(k3_xboole_0(B_111, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_558, c_605])).
% 5.63/2.08  tff(c_625, plain, (![B_111]: (m1_subset_1(k3_xboole_0(B_111, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_619])).
% 5.63/2.08  tff(c_581, plain, (![B_117, B_118, A_119]: (k9_subset_1(B_117, B_118, A_119)=k3_xboole_0(B_118, A_119) | ~r1_tarski(A_119, B_117))), inference(resolution, [status(thm)], [c_20, c_550])).
% 5.63/2.08  tff(c_595, plain, (![B_2, B_118]: (k9_subset_1(B_2, B_118, B_2)=k3_xboole_0(B_118, B_2))), inference(resolution, [status(thm)], [c_6, c_581])).
% 5.63/2.08  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.63/2.08  tff(c_621, plain, (![A_122, B_123, C_124]: (r1_tarski(k9_subset_1(A_122, B_123, C_124), A_122) | ~m1_subset_1(C_124, k1_zfmisc_1(A_122)))), inference(resolution, [status(thm)], [c_605, c_18])).
% 5.63/2.08  tff(c_707, plain, (![C_140, A_141, B_142]: (v2_tex_2(C_140, A_141) | ~v2_tex_2(B_142, A_141) | ~r1_tarski(C_140, B_142) | ~m1_subset_1(C_140, k1_zfmisc_1(u1_struct_0(A_141))) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.63/2.08  tff(c_1626, plain, (![A_262, B_263, C_264, A_265]: (v2_tex_2(k9_subset_1(A_262, B_263, C_264), A_265) | ~v2_tex_2(A_262, A_265) | ~m1_subset_1(k9_subset_1(A_262, B_263, C_264), k1_zfmisc_1(u1_struct_0(A_265))) | ~m1_subset_1(A_262, k1_zfmisc_1(u1_struct_0(A_265))) | ~l1_pre_topc(A_265) | ~m1_subset_1(C_264, k1_zfmisc_1(A_262)))), inference(resolution, [status(thm)], [c_621, c_707])).
% 5.63/2.08  tff(c_1660, plain, (![B_2, B_118, A_265]: (v2_tex_2(k9_subset_1(B_2, B_118, B_2), A_265) | ~v2_tex_2(B_2, A_265) | ~m1_subset_1(k3_xboole_0(B_118, B_2), k1_zfmisc_1(u1_struct_0(A_265))) | ~m1_subset_1(B_2, k1_zfmisc_1(u1_struct_0(A_265))) | ~l1_pre_topc(A_265) | ~m1_subset_1(B_2, k1_zfmisc_1(B_2)))), inference(superposition, [status(thm), theory('equality')], [c_595, c_1626])).
% 5.63/2.08  tff(c_3317, plain, (![B_446, B_447, A_448]: (v2_tex_2(k3_xboole_0(B_446, B_447), A_448) | ~v2_tex_2(B_447, A_448) | ~m1_subset_1(k3_xboole_0(B_446, B_447), k1_zfmisc_1(u1_struct_0(A_448))) | ~m1_subset_1(B_447, k1_zfmisc_1(u1_struct_0(A_448))) | ~l1_pre_topc(A_448) | ~m1_subset_1(B_447, k1_zfmisc_1(B_447)))), inference(demodulation, [status(thm), theory('equality')], [c_595, c_1660])).
% 5.63/2.08  tff(c_3356, plain, (![B_111]: (v2_tex_2(k3_xboole_0(B_111, '#skF_3'), '#skF_1') | ~v2_tex_2('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_625, c_3317])).
% 5.63/2.08  tff(c_3395, plain, (![B_111]: (v2_tex_2(k3_xboole_0(B_111, '#skF_3'), '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_499, c_3356])).
% 5.63/2.08  tff(c_3400, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_3395])).
% 5.63/2.08  tff(c_3403, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_3400])).
% 5.63/2.08  tff(c_3407, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3403])).
% 5.63/2.08  tff(c_3408, plain, (![B_111]: (v2_tex_2(k3_xboole_0(B_111, '#skF_3'), '#skF_1'))), inference(splitRight, [status(thm)], [c_3395])).
% 5.63/2.08  tff(c_561, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_558, c_24])).
% 5.63/2.08  tff(c_3439, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3408, c_561])).
% 5.63/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.63/2.08  
% 5.63/2.08  Inference rules
% 5.63/2.08  ----------------------
% 5.63/2.08  #Ref     : 0
% 5.63/2.08  #Sup     : 756
% 5.63/2.08  #Fact    : 0
% 5.63/2.08  #Define  : 0
% 5.63/2.08  #Split   : 7
% 5.63/2.08  #Chain   : 0
% 5.63/2.08  #Close   : 0
% 5.63/2.08  
% 5.63/2.08  Ordering : KBO
% 5.63/2.08  
% 5.63/2.08  Simplification rules
% 5.63/2.08  ----------------------
% 5.63/2.08  #Subsume      : 100
% 5.63/2.08  #Demod        : 625
% 5.63/2.08  #Tautology    : 204
% 5.63/2.08  #SimpNegUnit  : 4
% 5.63/2.08  #BackRed      : 4
% 5.63/2.08  
% 5.63/2.08  #Partial instantiations: 0
% 5.63/2.08  #Strategies tried      : 1
% 5.63/2.08  
% 5.63/2.08  Timing (in seconds)
% 5.63/2.08  ----------------------
% 5.63/2.08  Preprocessing        : 0.30
% 5.63/2.08  Parsing              : 0.16
% 5.63/2.08  CNF conversion       : 0.02
% 5.63/2.08  Main loop            : 0.97
% 5.63/2.08  Inferencing          : 0.36
% 5.63/2.08  Reduction            : 0.33
% 5.63/2.08  Demodulation         : 0.25
% 5.63/2.08  BG Simplification    : 0.04
% 5.63/2.09  Subsumption          : 0.17
% 5.63/2.09  Abstraction          : 0.06
% 5.63/2.09  MUC search           : 0.00
% 5.63/2.09  Cooper               : 0.00
% 5.63/2.09  Total                : 1.30
% 5.63/2.09  Index Insertion      : 0.00
% 5.63/2.09  Index Deletion       : 0.00
% 5.63/2.09  Index Matching       : 0.00
% 5.63/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------

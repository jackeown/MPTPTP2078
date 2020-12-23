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

% Result     : Theorem 21.26s
% Output     : CNFRefutation 21.30s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 121 expanded)
%              Number of leaves         :   28 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :  119 ( 252 expanded)
%              Number of equality atoms :   10 (  28 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_84,negated_conjecture,(
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

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_69,axiom,(
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

tff(f_39,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_186,plain,(
    ! [A_67,B_68,C_69] :
      ( k9_subset_1(A_67,B_68,C_69) = k3_xboole_0(B_68,C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_196,plain,(
    ! [B_68] : k9_subset_1(u1_struct_0('#skF_1'),B_68,'#skF_3') = k3_xboole_0(B_68,'#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_186])).

tff(c_26,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_222,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_26])).

tff(c_28,plain,
    ( v2_tex_2('#skF_3','#skF_1')
    | v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_47,plain,(
    v2_tex_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_327,plain,(
    ! [A_88,B_89,C_90] :
      ( m1_subset_1(k9_subset_1(A_88,B_89,C_90),k1_zfmisc_1(A_88))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(A_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_338,plain,(
    ! [B_68] :
      ( m1_subset_1(k3_xboole_0(B_68,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_327])).

tff(c_347,plain,(
    ! [B_68] : m1_subset_1(k3_xboole_0(B_68,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_338])).

tff(c_6,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = k3_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(k4_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_428,plain,(
    ! [C_105,A_106,B_107] :
      ( v2_tex_2(C_105,A_106)
      | ~ v2_tex_2(B_107,A_106)
      | ~ r1_tarski(C_105,B_107)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2122,plain,(
    ! [A_224,B_225,A_226] :
      ( v2_tex_2(k4_xboole_0(A_224,B_225),A_226)
      | ~ v2_tex_2(A_224,A_226)
      | ~ m1_subset_1(k4_xboole_0(A_224,B_225),k1_zfmisc_1(u1_struct_0(A_226)))
      | ~ m1_subset_1(A_224,k1_zfmisc_1(u1_struct_0(A_226)))
      | ~ l1_pre_topc(A_226) ) ),
    inference(resolution,[status(thm)],[c_4,c_428])).

tff(c_2128,plain,(
    ! [A_6,B_7,A_226] :
      ( v2_tex_2(k4_xboole_0(A_6,k4_xboole_0(A_6,B_7)),A_226)
      | ~ v2_tex_2(A_6,A_226)
      | ~ m1_subset_1(k3_xboole_0(A_6,B_7),k1_zfmisc_1(u1_struct_0(A_226)))
      | ~ m1_subset_1(A_6,k1_zfmisc_1(u1_struct_0(A_226)))
      | ~ l1_pre_topc(A_226) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_2122])).

tff(c_8461,plain,(
    ! [A_488,B_489,A_490] :
      ( v2_tex_2(k3_xboole_0(A_488,B_489),A_490)
      | ~ v2_tex_2(A_488,A_490)
      | ~ m1_subset_1(k3_xboole_0(A_488,B_489),k1_zfmisc_1(u1_struct_0(A_490)))
      | ~ m1_subset_1(A_488,k1_zfmisc_1(u1_struct_0(A_490)))
      | ~ l1_pre_topc(A_490) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2128])).

tff(c_8474,plain,(
    ! [B_68] :
      ( v2_tex_2(k3_xboole_0(B_68,'#skF_3'),'#skF_1')
      | ~ v2_tex_2(B_68,'#skF_1')
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_347,c_8461])).

tff(c_13633,plain,(
    ! [B_726] :
      ( v2_tex_2(k3_xboole_0(B_726,'#skF_3'),'#skF_1')
      | ~ v2_tex_2(B_726,'#skF_1')
      | ~ m1_subset_1(B_726,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_8474])).

tff(c_13673,plain,
    ( v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v2_tex_2('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_13633])).

tff(c_13691,plain,(
    v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_13673])).

tff(c_13693,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_222,c_13691])).

tff(c_13694,plain,(
    v2_tex_2('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_13834,plain,(
    ! [A_757,B_758,C_759] :
      ( k9_subset_1(A_757,B_758,C_759) = k3_xboole_0(B_758,C_759)
      | ~ m1_subset_1(C_759,k1_zfmisc_1(A_757)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_13844,plain,(
    ! [B_758] : k9_subset_1(u1_struct_0('#skF_1'),B_758,'#skF_3') = k3_xboole_0(B_758,'#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_13834])).

tff(c_13975,plain,(
    ! [A_778,B_779,C_780] :
      ( m1_subset_1(k9_subset_1(A_778,B_779,C_780),k1_zfmisc_1(A_778))
      | ~ m1_subset_1(C_780,k1_zfmisc_1(A_778)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_13986,plain,(
    ! [B_758] :
      ( m1_subset_1(k3_xboole_0(B_758,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13844,c_13975])).

tff(c_13995,plain,(
    ! [B_758] : m1_subset_1(k3_xboole_0(B_758,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_13986])).

tff(c_10,plain,(
    ! [A_10] : k2_subset_1(A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_11] : m1_subset_1(k2_subset_1(A_11),k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_35,plain,(
    ! [A_11] : m1_subset_1(A_11,k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_13846,plain,(
    ! [A_11,B_758] : k9_subset_1(A_11,B_758,A_11) = k3_xboole_0(B_758,A_11) ),
    inference(resolution,[status(thm)],[c_35,c_13834])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_15033,plain,(
    ! [A_859,B_860,C_861] :
      ( r1_tarski(k9_subset_1(A_859,B_860,C_861),A_859)
      | ~ m1_subset_1(C_861,k1_zfmisc_1(A_859)) ) ),
    inference(resolution,[status(thm)],[c_13975,c_20])).

tff(c_24,plain,(
    ! [C_28,A_22,B_26] :
      ( v2_tex_2(C_28,A_22)
      | ~ v2_tex_2(B_26,A_22)
      | ~ r1_tarski(C_28,B_26)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24395,plain,(
    ! [A_1288,B_1289,C_1290,A_1291] :
      ( v2_tex_2(k9_subset_1(A_1288,B_1289,C_1290),A_1291)
      | ~ v2_tex_2(A_1288,A_1291)
      | ~ m1_subset_1(k9_subset_1(A_1288,B_1289,C_1290),k1_zfmisc_1(u1_struct_0(A_1291)))
      | ~ m1_subset_1(A_1288,k1_zfmisc_1(u1_struct_0(A_1291)))
      | ~ l1_pre_topc(A_1291)
      | ~ m1_subset_1(C_1290,k1_zfmisc_1(A_1288)) ) ),
    inference(resolution,[status(thm)],[c_15033,c_24])).

tff(c_24441,plain,(
    ! [A_11,B_758,A_1291] :
      ( v2_tex_2(k9_subset_1(A_11,B_758,A_11),A_1291)
      | ~ v2_tex_2(A_11,A_1291)
      | ~ m1_subset_1(k3_xboole_0(B_758,A_11),k1_zfmisc_1(u1_struct_0(A_1291)))
      | ~ m1_subset_1(A_11,k1_zfmisc_1(u1_struct_0(A_1291)))
      | ~ l1_pre_topc(A_1291)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13846,c_24395])).

tff(c_66752,plain,(
    ! [B_2192,A_2193,A_2194] :
      ( v2_tex_2(k3_xboole_0(B_2192,A_2193),A_2194)
      | ~ v2_tex_2(A_2193,A_2194)
      | ~ m1_subset_1(k3_xboole_0(B_2192,A_2193),k1_zfmisc_1(u1_struct_0(A_2194)))
      | ~ m1_subset_1(A_2193,k1_zfmisc_1(u1_struct_0(A_2194)))
      | ~ l1_pre_topc(A_2194) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_13846,c_24441])).

tff(c_66791,plain,(
    ! [B_758] :
      ( v2_tex_2(k3_xboole_0(B_758,'#skF_3'),'#skF_1')
      | ~ v2_tex_2('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_13995,c_66752])).

tff(c_66828,plain,(
    ! [B_758] : v2_tex_2(k3_xboole_0(B_758,'#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_13694,c_66791])).

tff(c_13870,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13844,c_26])).

tff(c_66844,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66828,c_13870])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:41:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.26/13.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.26/13.75  
% 21.26/13.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.30/13.75  %$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 21.30/13.75  
% 21.30/13.75  %Foreground sorts:
% 21.30/13.75  
% 21.30/13.75  
% 21.30/13.75  %Background operators:
% 21.30/13.75  
% 21.30/13.75  
% 21.30/13.75  %Foreground operators:
% 21.30/13.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.30/13.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 21.30/13.75  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 21.30/13.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.30/13.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 21.30/13.75  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 21.30/13.75  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 21.30/13.75  tff('#skF_2', type, '#skF_2': $i).
% 21.30/13.75  tff('#skF_3', type, '#skF_3': $i).
% 21.30/13.75  tff('#skF_1', type, '#skF_1': $i).
% 21.30/13.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 21.30/13.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.30/13.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.30/13.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 21.30/13.75  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 21.30/13.75  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 21.30/13.75  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 21.30/13.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 21.30/13.75  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 21.30/13.75  
% 21.30/13.76  tff(f_84, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tex_2)).
% 21.30/13.76  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 21.30/13.76  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 21.30/13.76  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 21.30/13.76  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 21.30/13.76  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_tex_2)).
% 21.30/13.76  tff(f_39, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 21.30/13.76  tff(f_41, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 21.30/13.76  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 21.30/13.76  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 21.30/13.76  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 21.30/13.76  tff(c_186, plain, (![A_67, B_68, C_69]: (k9_subset_1(A_67, B_68, C_69)=k3_xboole_0(B_68, C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 21.30/13.76  tff(c_196, plain, (![B_68]: (k9_subset_1(u1_struct_0('#skF_1'), B_68, '#skF_3')=k3_xboole_0(B_68, '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_186])).
% 21.30/13.76  tff(c_26, plain, (~v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 21.30/13.76  tff(c_222, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_26])).
% 21.30/13.76  tff(c_28, plain, (v2_tex_2('#skF_3', '#skF_1') | v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 21.30/13.76  tff(c_47, plain, (v2_tex_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_28])).
% 21.30/13.76  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 21.30/13.76  tff(c_327, plain, (![A_88, B_89, C_90]: (m1_subset_1(k9_subset_1(A_88, B_89, C_90), k1_zfmisc_1(A_88)) | ~m1_subset_1(C_90, k1_zfmisc_1(A_88)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 21.30/13.76  tff(c_338, plain, (![B_68]: (m1_subset_1(k3_xboole_0(B_68, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_196, c_327])).
% 21.30/13.76  tff(c_347, plain, (![B_68]: (m1_subset_1(k3_xboole_0(B_68, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_338])).
% 21.30/13.76  tff(c_6, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k4_xboole_0(A_6, B_7))=k3_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 21.30/13.76  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 21.30/13.76  tff(c_428, plain, (![C_105, A_106, B_107]: (v2_tex_2(C_105, A_106) | ~v2_tex_2(B_107, A_106) | ~r1_tarski(C_105, B_107) | ~m1_subset_1(C_105, k1_zfmisc_1(u1_struct_0(A_106))) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_69])).
% 21.30/13.76  tff(c_2122, plain, (![A_224, B_225, A_226]: (v2_tex_2(k4_xboole_0(A_224, B_225), A_226) | ~v2_tex_2(A_224, A_226) | ~m1_subset_1(k4_xboole_0(A_224, B_225), k1_zfmisc_1(u1_struct_0(A_226))) | ~m1_subset_1(A_224, k1_zfmisc_1(u1_struct_0(A_226))) | ~l1_pre_topc(A_226))), inference(resolution, [status(thm)], [c_4, c_428])).
% 21.30/13.76  tff(c_2128, plain, (![A_6, B_7, A_226]: (v2_tex_2(k4_xboole_0(A_6, k4_xboole_0(A_6, B_7)), A_226) | ~v2_tex_2(A_6, A_226) | ~m1_subset_1(k3_xboole_0(A_6, B_7), k1_zfmisc_1(u1_struct_0(A_226))) | ~m1_subset_1(A_6, k1_zfmisc_1(u1_struct_0(A_226))) | ~l1_pre_topc(A_226))), inference(superposition, [status(thm), theory('equality')], [c_6, c_2122])).
% 21.30/13.76  tff(c_8461, plain, (![A_488, B_489, A_490]: (v2_tex_2(k3_xboole_0(A_488, B_489), A_490) | ~v2_tex_2(A_488, A_490) | ~m1_subset_1(k3_xboole_0(A_488, B_489), k1_zfmisc_1(u1_struct_0(A_490))) | ~m1_subset_1(A_488, k1_zfmisc_1(u1_struct_0(A_490))) | ~l1_pre_topc(A_490))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2128])).
% 21.30/13.76  tff(c_8474, plain, (![B_68]: (v2_tex_2(k3_xboole_0(B_68, '#skF_3'), '#skF_1') | ~v2_tex_2(B_68, '#skF_1') | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_347, c_8461])).
% 21.30/13.76  tff(c_13633, plain, (![B_726]: (v2_tex_2(k3_xboole_0(B_726, '#skF_3'), '#skF_1') | ~v2_tex_2(B_726, '#skF_1') | ~m1_subset_1(B_726, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_8474])).
% 21.30/13.76  tff(c_13673, plain, (v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v2_tex_2('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_13633])).
% 21.30/13.76  tff(c_13691, plain, (v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_13673])).
% 21.30/13.76  tff(c_13693, plain, $false, inference(negUnitSimplification, [status(thm)], [c_222, c_13691])).
% 21.30/13.76  tff(c_13694, plain, (v2_tex_2('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_28])).
% 21.30/13.76  tff(c_13834, plain, (![A_757, B_758, C_759]: (k9_subset_1(A_757, B_758, C_759)=k3_xboole_0(B_758, C_759) | ~m1_subset_1(C_759, k1_zfmisc_1(A_757)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 21.30/13.76  tff(c_13844, plain, (![B_758]: (k9_subset_1(u1_struct_0('#skF_1'), B_758, '#skF_3')=k3_xboole_0(B_758, '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_13834])).
% 21.30/13.76  tff(c_13975, plain, (![A_778, B_779, C_780]: (m1_subset_1(k9_subset_1(A_778, B_779, C_780), k1_zfmisc_1(A_778)) | ~m1_subset_1(C_780, k1_zfmisc_1(A_778)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 21.30/13.76  tff(c_13986, plain, (![B_758]: (m1_subset_1(k3_xboole_0(B_758, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_13844, c_13975])).
% 21.30/13.76  tff(c_13995, plain, (![B_758]: (m1_subset_1(k3_xboole_0(B_758, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_13986])).
% 21.30/13.76  tff(c_10, plain, (![A_10]: (k2_subset_1(A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 21.30/13.76  tff(c_12, plain, (![A_11]: (m1_subset_1(k2_subset_1(A_11), k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 21.30/13.76  tff(c_35, plain, (![A_11]: (m1_subset_1(A_11, k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 21.30/13.76  tff(c_13846, plain, (![A_11, B_758]: (k9_subset_1(A_11, B_758, A_11)=k3_xboole_0(B_758, A_11))), inference(resolution, [status(thm)], [c_35, c_13834])).
% 21.30/13.76  tff(c_20, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~m1_subset_1(A_20, k1_zfmisc_1(B_21)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 21.30/13.76  tff(c_15033, plain, (![A_859, B_860, C_861]: (r1_tarski(k9_subset_1(A_859, B_860, C_861), A_859) | ~m1_subset_1(C_861, k1_zfmisc_1(A_859)))), inference(resolution, [status(thm)], [c_13975, c_20])).
% 21.30/13.76  tff(c_24, plain, (![C_28, A_22, B_26]: (v2_tex_2(C_28, A_22) | ~v2_tex_2(B_26, A_22) | ~r1_tarski(C_28, B_26) | ~m1_subset_1(C_28, k1_zfmisc_1(u1_struct_0(A_22))) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_69])).
% 21.30/13.76  tff(c_24395, plain, (![A_1288, B_1289, C_1290, A_1291]: (v2_tex_2(k9_subset_1(A_1288, B_1289, C_1290), A_1291) | ~v2_tex_2(A_1288, A_1291) | ~m1_subset_1(k9_subset_1(A_1288, B_1289, C_1290), k1_zfmisc_1(u1_struct_0(A_1291))) | ~m1_subset_1(A_1288, k1_zfmisc_1(u1_struct_0(A_1291))) | ~l1_pre_topc(A_1291) | ~m1_subset_1(C_1290, k1_zfmisc_1(A_1288)))), inference(resolution, [status(thm)], [c_15033, c_24])).
% 21.30/13.76  tff(c_24441, plain, (![A_11, B_758, A_1291]: (v2_tex_2(k9_subset_1(A_11, B_758, A_11), A_1291) | ~v2_tex_2(A_11, A_1291) | ~m1_subset_1(k3_xboole_0(B_758, A_11), k1_zfmisc_1(u1_struct_0(A_1291))) | ~m1_subset_1(A_11, k1_zfmisc_1(u1_struct_0(A_1291))) | ~l1_pre_topc(A_1291) | ~m1_subset_1(A_11, k1_zfmisc_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_13846, c_24395])).
% 21.30/13.76  tff(c_66752, plain, (![B_2192, A_2193, A_2194]: (v2_tex_2(k3_xboole_0(B_2192, A_2193), A_2194) | ~v2_tex_2(A_2193, A_2194) | ~m1_subset_1(k3_xboole_0(B_2192, A_2193), k1_zfmisc_1(u1_struct_0(A_2194))) | ~m1_subset_1(A_2193, k1_zfmisc_1(u1_struct_0(A_2194))) | ~l1_pre_topc(A_2194))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_13846, c_24441])).
% 21.30/13.76  tff(c_66791, plain, (![B_758]: (v2_tex_2(k3_xboole_0(B_758, '#skF_3'), '#skF_1') | ~v2_tex_2('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_13995, c_66752])).
% 21.30/13.76  tff(c_66828, plain, (![B_758]: (v2_tex_2(k3_xboole_0(B_758, '#skF_3'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_13694, c_66791])).
% 21.30/13.76  tff(c_13870, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13844, c_26])).
% 21.30/13.76  tff(c_66844, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66828, c_13870])).
% 21.30/13.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.30/13.76  
% 21.30/13.76  Inference rules
% 21.30/13.76  ----------------------
% 21.30/13.76  #Ref     : 0
% 21.30/13.76  #Sup     : 14378
% 21.30/13.76  #Fact    : 0
% 21.30/13.76  #Define  : 0
% 21.30/13.76  #Split   : 2
% 21.30/13.76  #Chain   : 0
% 21.30/13.76  #Close   : 0
% 21.30/13.76  
% 21.30/13.76  Ordering : KBO
% 21.30/13.76  
% 21.30/13.76  Simplification rules
% 21.30/13.76  ----------------------
% 21.30/13.76  #Subsume      : 658
% 21.30/13.76  #Demod        : 3051
% 21.30/13.76  #Tautology    : 2282
% 21.30/13.76  #SimpNegUnit  : 8
% 21.30/13.76  #BackRed      : 5
% 21.30/13.76  
% 21.30/13.76  #Partial instantiations: 0
% 21.30/13.76  #Strategies tried      : 1
% 21.30/13.76  
% 21.30/13.76  Timing (in seconds)
% 21.30/13.76  ----------------------
% 21.30/13.77  Preprocessing        : 0.39
% 21.30/13.77  Parsing              : 0.23
% 21.30/13.77  CNF conversion       : 0.02
% 21.30/13.77  Main loop            : 12.48
% 21.30/13.77  Inferencing          : 1.69
% 21.30/13.77  Reduction            : 4.92
% 21.30/13.77  Demodulation         : 4.31
% 21.30/13.77  BG Simplification    : 0.22
% 21.30/13.77  Subsumption          : 4.99
% 21.30/13.77  Abstraction          : 0.26
% 21.30/13.77  MUC search           : 0.00
% 21.30/13.77  Cooper               : 0.00
% 21.30/13.77  Total                : 12.90
% 21.30/13.77  Index Insertion      : 0.00
% 21.30/13.77  Index Deletion       : 0.00
% 21.30/13.77  Index Matching       : 0.00
% 21.30/13.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------

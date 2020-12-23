%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:12 EST 2020

% Result     : Theorem 42.26s
% Output     : CNFRefutation 42.26s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 330 expanded)
%              Number of leaves         :   23 ( 122 expanded)
%              Depth                    :    9
%              Number of atoms          :  164 ( 707 expanded)
%              Number of equality atoms :   26 ( 135 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_54638,plain,(
    ! [A_1266,B_1267,C_1268] :
      ( k9_subset_1(A_1266,B_1267,C_1268) = k3_xboole_0(B_1267,C_1268)
      | ~ m1_subset_1(C_1268,k1_zfmisc_1(A_1266)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_54728,plain,(
    ! [B_1276] : k9_subset_1(u1_struct_0('#skF_1'),B_1276,'#skF_2') = k3_xboole_0(B_1276,'#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_54638])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_54649,plain,(
    ! [B_1267] : k9_subset_1(u1_struct_0('#skF_1'),B_1267,'#skF_3') = k3_xboole_0(B_1267,'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_54638])).

tff(c_54671,plain,(
    ! [A_1270,C_1271,B_1272] :
      ( k9_subset_1(A_1270,C_1271,B_1272) = k9_subset_1(A_1270,B_1272,C_1271)
      | ~ m1_subset_1(C_1271,k1_zfmisc_1(A_1270)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_54677,plain,(
    ! [B_1272] : k9_subset_1(u1_struct_0('#skF_1'),B_1272,'#skF_3') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_1272) ),
    inference(resolution,[status(thm)],[c_26,c_54671])).

tff(c_54683,plain,(
    ! [B_1272] : k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_1272) = k3_xboole_0(B_1272,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54649,c_54677])).

tff(c_54735,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_54728,c_54683])).

tff(c_22,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_54651,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54649,c_22])).

tff(c_54755,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54735,c_54651])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_54845,plain,(
    ! [B_1284,B_1285,A_1286] :
      ( k9_subset_1(B_1284,B_1285,A_1286) = k3_xboole_0(B_1285,A_1286)
      | ~ r1_tarski(A_1286,B_1284) ) ),
    inference(resolution,[status(thm)],[c_18,c_54638])).

tff(c_54866,plain,(
    ! [B_1287,B_1288] : k9_subset_1(B_1287,B_1288,B_1287) = k3_xboole_0(B_1288,B_1287) ),
    inference(resolution,[status(thm)],[c_6,c_54845])).

tff(c_54629,plain,(
    ! [A_1260,B_1261,C_1262] :
      ( m1_subset_1(k9_subset_1(A_1260,B_1261,C_1262),k1_zfmisc_1(A_1260))
      | ~ m1_subset_1(C_1262,k1_zfmisc_1(A_1260)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_54633,plain,(
    ! [A_1260,B_1261,C_1262] :
      ( r1_tarski(k9_subset_1(A_1260,B_1261,C_1262),A_1260)
      | ~ m1_subset_1(C_1262,k1_zfmisc_1(A_1260)) ) ),
    inference(resolution,[status(thm)],[c_54629,c_16])).

tff(c_55077,plain,(
    ! [B_1300,B_1301] :
      ( r1_tarski(k3_xboole_0(B_1300,B_1301),B_1301)
      | ~ m1_subset_1(B_1301,k1_zfmisc_1(B_1301)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54866,c_54633])).

tff(c_55094,plain,
    ( r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_54735,c_55077])).

tff(c_55196,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_55094])).

tff(c_55230,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_55196])).

tff(c_55234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_55230])).

tff(c_55236,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_55094])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_71,plain,(
    ! [A_36,B_37,C_38] :
      ( k9_subset_1(A_36,B_37,C_38) = k3_xboole_0(B_37,C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_101,plain,(
    ! [B_41,B_42,A_43] :
      ( k9_subset_1(B_41,B_42,A_43) = k3_xboole_0(B_42,A_43)
      | ~ r1_tarski(A_43,B_41) ) ),
    inference(resolution,[status(thm)],[c_18,c_71])).

tff(c_112,plain,(
    ! [B_2,B_42] : k9_subset_1(B_2,B_42,B_2) = k3_xboole_0(B_42,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_101])).

tff(c_80,plain,(
    ! [B_37] : k9_subset_1(u1_struct_0('#skF_1'),B_37,'#skF_2') = k3_xboole_0(B_37,'#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_71])).

tff(c_151,plain,(
    ! [A_50,C_51,B_52] :
      ( k9_subset_1(A_50,C_51,B_52) = k9_subset_1(A_50,B_52,C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_161,plain,(
    ! [B_52] : k9_subset_1(u1_struct_0('#skF_1'),B_52,'#skF_2') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_52) ),
    inference(resolution,[status(thm)],[c_28,c_151])).

tff(c_245,plain,(
    ! [B_57] : k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_57) = k3_xboole_0(B_57,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_161])).

tff(c_270,plain,(
    k3_xboole_0(u1_struct_0('#skF_1'),'#skF_2') = k3_xboole_0('#skF_2',u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_245])).

tff(c_122,plain,(
    ! [A_46,B_47,C_48] :
      ( m1_subset_1(k9_subset_1(A_46,B_47,C_48),k1_zfmisc_1(A_46))
      | ~ m1_subset_1(C_48,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_365,plain,(
    ! [A_62,B_63,C_64] :
      ( r1_tarski(k9_subset_1(A_62,B_63,C_64),A_62)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(A_62)) ) ),
    inference(resolution,[status(thm)],[c_122,c_16])).

tff(c_469,plain,(
    ! [B_70,B_71] :
      ( r1_tarski(k3_xboole_0(B_70,B_71),B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(B_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_365])).

tff(c_480,plain,
    ( r1_tarski(k3_xboole_0('#skF_2',u1_struct_0('#skF_1')),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_469])).

tff(c_2038,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_480])).

tff(c_2054,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_2038])).

tff(c_2058,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2054])).

tff(c_2060,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_480])).

tff(c_24,plain,
    ( v2_tex_2('#skF_3','#skF_1')
    | v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_33,plain,(
    v2_tex_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_133,plain,(
    ! [B_37] :
      ( m1_subset_1(k3_xboole_0(B_37,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_122])).

tff(c_140,plain,(
    ! [B_37] : m1_subset_1(k3_xboole_0(B_37,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_133])).

tff(c_20,plain,(
    ! [C_22,A_16,B_20] :
      ( v2_tex_2(C_22,A_16)
      | ~ v2_tex_2(B_20,A_16)
      | ~ r1_tarski(C_22,B_20)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3755,plain,(
    ! [A_175,B_176,C_177,A_178] :
      ( v2_tex_2(k9_subset_1(A_175,B_176,C_177),A_178)
      | ~ v2_tex_2(A_175,A_178)
      | ~ m1_subset_1(k9_subset_1(A_175,B_176,C_177),k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ m1_subset_1(A_175,k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ l1_pre_topc(A_178)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(A_175)) ) ),
    inference(resolution,[status(thm)],[c_365,c_20])).

tff(c_3807,plain,(
    ! [B_2,B_42,A_178] :
      ( v2_tex_2(k9_subset_1(B_2,B_42,B_2),A_178)
      | ~ v2_tex_2(B_2,A_178)
      | ~ m1_subset_1(k3_xboole_0(B_42,B_2),k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ l1_pre_topc(A_178)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_3755])).

tff(c_54339,plain,(
    ! [B_1249,B_1250,A_1251] :
      ( v2_tex_2(k3_xboole_0(B_1249,B_1250),A_1251)
      | ~ v2_tex_2(B_1250,A_1251)
      | ~ m1_subset_1(k3_xboole_0(B_1249,B_1250),k1_zfmisc_1(u1_struct_0(A_1251)))
      | ~ m1_subset_1(B_1250,k1_zfmisc_1(u1_struct_0(A_1251)))
      | ~ l1_pre_topc(A_1251)
      | ~ m1_subset_1(B_1250,k1_zfmisc_1(B_1250)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_3807])).

tff(c_54465,plain,(
    ! [B_37] :
      ( v2_tex_2(k3_xboole_0(B_37,'#skF_2'),'#skF_1')
      | ~ v2_tex_2('#skF_2','#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_140,c_54339])).

tff(c_54583,plain,(
    ! [B_37] : v2_tex_2(k3_xboole_0(B_37,'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2060,c_30,c_28,c_33,c_54465])).

tff(c_79,plain,(
    ! [B_37] : k9_subset_1(u1_struct_0('#skF_1'),B_37,'#skF_3') = k3_xboole_0(B_37,'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_71])).

tff(c_159,plain,(
    ! [B_52] : k9_subset_1(u1_struct_0('#skF_1'),B_52,'#skF_3') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_52) ),
    inference(resolution,[status(thm)],[c_26,c_151])).

tff(c_194,plain,(
    ! [B_56] : k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_56) = k3_xboole_0(B_56,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_159])).

tff(c_208,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_80])).

tff(c_82,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_22])).

tff(c_233,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_82])).

tff(c_54588,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54583,c_233])).

tff(c_54589,plain,(
    v2_tex_2('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_54652,plain,(
    ! [B_1269] : k9_subset_1(u1_struct_0('#skF_1'),B_1269,'#skF_3') = k3_xboole_0(B_1269,'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_54638])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8] :
      ( m1_subset_1(k9_subset_1(A_6,B_7,C_8),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(C_8,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_54661,plain,(
    ! [B_1269] :
      ( m1_subset_1(k3_xboole_0(B_1269,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54652,c_10])).

tff(c_54669,plain,(
    ! [B_1269] : m1_subset_1(k3_xboole_0(B_1269,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_54661])).

tff(c_54865,plain,(
    ! [B_2,B_1285] : k9_subset_1(B_2,B_1285,B_2) = k3_xboole_0(B_1285,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_54845])).

tff(c_54770,plain,(
    ! [C_1278,A_1279,B_1280] :
      ( v2_tex_2(C_1278,A_1279)
      | ~ v2_tex_2(B_1280,A_1279)
      | ~ r1_tarski(C_1278,B_1280)
      | ~ m1_subset_1(C_1278,k1_zfmisc_1(u1_struct_0(A_1279)))
      | ~ m1_subset_1(B_1280,k1_zfmisc_1(u1_struct_0(A_1279)))
      | ~ l1_pre_topc(A_1279) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_58346,plain,(
    ! [A_1403,B_1404,C_1405,A_1406] :
      ( v2_tex_2(k9_subset_1(A_1403,B_1404,C_1405),A_1406)
      | ~ v2_tex_2(A_1403,A_1406)
      | ~ m1_subset_1(k9_subset_1(A_1403,B_1404,C_1405),k1_zfmisc_1(u1_struct_0(A_1406)))
      | ~ m1_subset_1(A_1403,k1_zfmisc_1(u1_struct_0(A_1406)))
      | ~ l1_pre_topc(A_1406)
      | ~ m1_subset_1(C_1405,k1_zfmisc_1(A_1403)) ) ),
    inference(resolution,[status(thm)],[c_54633,c_54770])).

tff(c_58388,plain,(
    ! [B_2,B_1285,A_1406] :
      ( v2_tex_2(k9_subset_1(B_2,B_1285,B_2),A_1406)
      | ~ v2_tex_2(B_2,A_1406)
      | ~ m1_subset_1(k3_xboole_0(B_1285,B_2),k1_zfmisc_1(u1_struct_0(A_1406)))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(u1_struct_0(A_1406)))
      | ~ l1_pre_topc(A_1406)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54865,c_58346])).

tff(c_105233,plain,(
    ! [B_2425,B_2426,A_2427] :
      ( v2_tex_2(k3_xboole_0(B_2425,B_2426),A_2427)
      | ~ v2_tex_2(B_2426,A_2427)
      | ~ m1_subset_1(k3_xboole_0(B_2425,B_2426),k1_zfmisc_1(u1_struct_0(A_2427)))
      | ~ m1_subset_1(B_2426,k1_zfmisc_1(u1_struct_0(A_2427)))
      | ~ l1_pre_topc(A_2427)
      | ~ m1_subset_1(B_2426,k1_zfmisc_1(B_2426)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54865,c_58388])).

tff(c_105355,plain,(
    ! [B_1269] :
      ( v2_tex_2(k3_xboole_0(B_1269,'#skF_3'),'#skF_1')
      | ~ v2_tex_2('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_54669,c_105233])).

tff(c_105471,plain,(
    ! [B_2428] : v2_tex_2(k3_xboole_0(B_2428,'#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55236,c_30,c_26,c_54589,c_105355])).

tff(c_105499,plain,(
    v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_54735,c_105471])).

tff(c_105501,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54755,c_105499])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:54:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 42.26/31.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 42.26/31.34  
% 42.26/31.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 42.26/31.35  %$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 42.26/31.35  
% 42.26/31.35  %Foreground sorts:
% 42.26/31.35  
% 42.26/31.35  
% 42.26/31.35  %Background operators:
% 42.26/31.35  
% 42.26/31.35  
% 42.26/31.35  %Foreground operators:
% 42.26/31.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 42.26/31.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 42.26/31.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 42.26/31.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 42.26/31.35  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 42.26/31.35  tff('#skF_2', type, '#skF_2': $i).
% 42.26/31.35  tff('#skF_3', type, '#skF_3': $i).
% 42.26/31.35  tff('#skF_1', type, '#skF_1': $i).
% 42.26/31.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 42.26/31.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 42.26/31.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 42.26/31.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 42.26/31.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 42.26/31.35  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 42.26/31.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 42.26/31.35  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 42.26/31.35  
% 42.26/31.36  tff(f_78, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tex_2)).
% 42.26/31.36  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 42.26/31.36  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 42.26/31.36  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 42.26/31.36  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 42.26/31.36  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 42.26/31.36  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_tex_2)).
% 42.26/31.36  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 42.26/31.36  tff(c_54638, plain, (![A_1266, B_1267, C_1268]: (k9_subset_1(A_1266, B_1267, C_1268)=k3_xboole_0(B_1267, C_1268) | ~m1_subset_1(C_1268, k1_zfmisc_1(A_1266)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 42.26/31.36  tff(c_54728, plain, (![B_1276]: (k9_subset_1(u1_struct_0('#skF_1'), B_1276, '#skF_2')=k3_xboole_0(B_1276, '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_54638])).
% 42.26/31.36  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 42.26/31.36  tff(c_54649, plain, (![B_1267]: (k9_subset_1(u1_struct_0('#skF_1'), B_1267, '#skF_3')=k3_xboole_0(B_1267, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_54638])).
% 42.26/31.36  tff(c_54671, plain, (![A_1270, C_1271, B_1272]: (k9_subset_1(A_1270, C_1271, B_1272)=k9_subset_1(A_1270, B_1272, C_1271) | ~m1_subset_1(C_1271, k1_zfmisc_1(A_1270)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 42.26/31.36  tff(c_54677, plain, (![B_1272]: (k9_subset_1(u1_struct_0('#skF_1'), B_1272, '#skF_3')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_1272))), inference(resolution, [status(thm)], [c_26, c_54671])).
% 42.26/31.36  tff(c_54683, plain, (![B_1272]: (k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_1272)=k3_xboole_0(B_1272, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54649, c_54677])).
% 42.26/31.36  tff(c_54735, plain, (k3_xboole_0('#skF_2', '#skF_3')=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_54728, c_54683])).
% 42.26/31.36  tff(c_22, plain, (~v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 42.26/31.36  tff(c_54651, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54649, c_22])).
% 42.26/31.36  tff(c_54755, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54735, c_54651])).
% 42.26/31.36  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 42.26/31.36  tff(c_18, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 42.26/31.36  tff(c_54845, plain, (![B_1284, B_1285, A_1286]: (k9_subset_1(B_1284, B_1285, A_1286)=k3_xboole_0(B_1285, A_1286) | ~r1_tarski(A_1286, B_1284))), inference(resolution, [status(thm)], [c_18, c_54638])).
% 42.26/31.36  tff(c_54866, plain, (![B_1287, B_1288]: (k9_subset_1(B_1287, B_1288, B_1287)=k3_xboole_0(B_1288, B_1287))), inference(resolution, [status(thm)], [c_6, c_54845])).
% 42.26/31.36  tff(c_54629, plain, (![A_1260, B_1261, C_1262]: (m1_subset_1(k9_subset_1(A_1260, B_1261, C_1262), k1_zfmisc_1(A_1260)) | ~m1_subset_1(C_1262, k1_zfmisc_1(A_1260)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 42.26/31.36  tff(c_16, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 42.26/31.36  tff(c_54633, plain, (![A_1260, B_1261, C_1262]: (r1_tarski(k9_subset_1(A_1260, B_1261, C_1262), A_1260) | ~m1_subset_1(C_1262, k1_zfmisc_1(A_1260)))), inference(resolution, [status(thm)], [c_54629, c_16])).
% 42.26/31.36  tff(c_55077, plain, (![B_1300, B_1301]: (r1_tarski(k3_xboole_0(B_1300, B_1301), B_1301) | ~m1_subset_1(B_1301, k1_zfmisc_1(B_1301)))), inference(superposition, [status(thm), theory('equality')], [c_54866, c_54633])).
% 42.26/31.36  tff(c_55094, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_54735, c_55077])).
% 42.26/31.36  tff(c_55196, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_55094])).
% 42.26/31.36  tff(c_55230, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_55196])).
% 42.26/31.36  tff(c_55234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_55230])).
% 42.26/31.36  tff(c_55236, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_55094])).
% 42.26/31.36  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 42.26/31.36  tff(c_71, plain, (![A_36, B_37, C_38]: (k9_subset_1(A_36, B_37, C_38)=k3_xboole_0(B_37, C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 42.26/31.36  tff(c_101, plain, (![B_41, B_42, A_43]: (k9_subset_1(B_41, B_42, A_43)=k3_xboole_0(B_42, A_43) | ~r1_tarski(A_43, B_41))), inference(resolution, [status(thm)], [c_18, c_71])).
% 42.26/31.36  tff(c_112, plain, (![B_2, B_42]: (k9_subset_1(B_2, B_42, B_2)=k3_xboole_0(B_42, B_2))), inference(resolution, [status(thm)], [c_6, c_101])).
% 42.26/31.36  tff(c_80, plain, (![B_37]: (k9_subset_1(u1_struct_0('#skF_1'), B_37, '#skF_2')=k3_xboole_0(B_37, '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_71])).
% 42.26/31.36  tff(c_151, plain, (![A_50, C_51, B_52]: (k9_subset_1(A_50, C_51, B_52)=k9_subset_1(A_50, B_52, C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 42.26/31.36  tff(c_161, plain, (![B_52]: (k9_subset_1(u1_struct_0('#skF_1'), B_52, '#skF_2')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_52))), inference(resolution, [status(thm)], [c_28, c_151])).
% 42.26/31.36  tff(c_245, plain, (![B_57]: (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_57)=k3_xboole_0(B_57, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_161])).
% 42.26/31.36  tff(c_270, plain, (k3_xboole_0(u1_struct_0('#skF_1'), '#skF_2')=k3_xboole_0('#skF_2', u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_245])).
% 42.26/31.36  tff(c_122, plain, (![A_46, B_47, C_48]: (m1_subset_1(k9_subset_1(A_46, B_47, C_48), k1_zfmisc_1(A_46)) | ~m1_subset_1(C_48, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 42.26/31.36  tff(c_365, plain, (![A_62, B_63, C_64]: (r1_tarski(k9_subset_1(A_62, B_63, C_64), A_62) | ~m1_subset_1(C_64, k1_zfmisc_1(A_62)))), inference(resolution, [status(thm)], [c_122, c_16])).
% 42.26/31.36  tff(c_469, plain, (![B_70, B_71]: (r1_tarski(k3_xboole_0(B_70, B_71), B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(B_71)))), inference(superposition, [status(thm), theory('equality')], [c_112, c_365])).
% 42.26/31.36  tff(c_480, plain, (r1_tarski(k3_xboole_0('#skF_2', u1_struct_0('#skF_1')), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_270, c_469])).
% 42.26/31.36  tff(c_2038, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_480])).
% 42.26/31.36  tff(c_2054, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_18, c_2038])).
% 42.26/31.36  tff(c_2058, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2054])).
% 42.26/31.36  tff(c_2060, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(splitRight, [status(thm)], [c_480])).
% 42.26/31.36  tff(c_24, plain, (v2_tex_2('#skF_3', '#skF_1') | v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 42.26/31.36  tff(c_33, plain, (v2_tex_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_24])).
% 42.26/31.36  tff(c_133, plain, (![B_37]: (m1_subset_1(k3_xboole_0(B_37, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_80, c_122])).
% 42.26/31.36  tff(c_140, plain, (![B_37]: (m1_subset_1(k3_xboole_0(B_37, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_133])).
% 42.26/31.36  tff(c_20, plain, (![C_22, A_16, B_20]: (v2_tex_2(C_22, A_16) | ~v2_tex_2(B_20, A_16) | ~r1_tarski(C_22, B_20) | ~m1_subset_1(C_22, k1_zfmisc_1(u1_struct_0(A_16))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 42.26/31.36  tff(c_3755, plain, (![A_175, B_176, C_177, A_178]: (v2_tex_2(k9_subset_1(A_175, B_176, C_177), A_178) | ~v2_tex_2(A_175, A_178) | ~m1_subset_1(k9_subset_1(A_175, B_176, C_177), k1_zfmisc_1(u1_struct_0(A_178))) | ~m1_subset_1(A_175, k1_zfmisc_1(u1_struct_0(A_178))) | ~l1_pre_topc(A_178) | ~m1_subset_1(C_177, k1_zfmisc_1(A_175)))), inference(resolution, [status(thm)], [c_365, c_20])).
% 42.26/31.36  tff(c_3807, plain, (![B_2, B_42, A_178]: (v2_tex_2(k9_subset_1(B_2, B_42, B_2), A_178) | ~v2_tex_2(B_2, A_178) | ~m1_subset_1(k3_xboole_0(B_42, B_2), k1_zfmisc_1(u1_struct_0(A_178))) | ~m1_subset_1(B_2, k1_zfmisc_1(u1_struct_0(A_178))) | ~l1_pre_topc(A_178) | ~m1_subset_1(B_2, k1_zfmisc_1(B_2)))), inference(superposition, [status(thm), theory('equality')], [c_112, c_3755])).
% 42.26/31.36  tff(c_54339, plain, (![B_1249, B_1250, A_1251]: (v2_tex_2(k3_xboole_0(B_1249, B_1250), A_1251) | ~v2_tex_2(B_1250, A_1251) | ~m1_subset_1(k3_xboole_0(B_1249, B_1250), k1_zfmisc_1(u1_struct_0(A_1251))) | ~m1_subset_1(B_1250, k1_zfmisc_1(u1_struct_0(A_1251))) | ~l1_pre_topc(A_1251) | ~m1_subset_1(B_1250, k1_zfmisc_1(B_1250)))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_3807])).
% 42.26/31.36  tff(c_54465, plain, (![B_37]: (v2_tex_2(k3_xboole_0(B_37, '#skF_2'), '#skF_1') | ~v2_tex_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_140, c_54339])).
% 42.26/31.36  tff(c_54583, plain, (![B_37]: (v2_tex_2(k3_xboole_0(B_37, '#skF_2'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2060, c_30, c_28, c_33, c_54465])).
% 42.26/31.36  tff(c_79, plain, (![B_37]: (k9_subset_1(u1_struct_0('#skF_1'), B_37, '#skF_3')=k3_xboole_0(B_37, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_71])).
% 42.26/31.36  tff(c_159, plain, (![B_52]: (k9_subset_1(u1_struct_0('#skF_1'), B_52, '#skF_3')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_52))), inference(resolution, [status(thm)], [c_26, c_151])).
% 42.26/31.36  tff(c_194, plain, (![B_56]: (k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_56)=k3_xboole_0(B_56, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_159])).
% 42.26/31.36  tff(c_208, plain, (k3_xboole_0('#skF_2', '#skF_3')=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_194, c_80])).
% 42.26/31.36  tff(c_82, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_22])).
% 42.26/31.36  tff(c_233, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_82])).
% 42.26/31.36  tff(c_54588, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54583, c_233])).
% 42.26/31.36  tff(c_54589, plain, (v2_tex_2('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_24])).
% 42.26/31.36  tff(c_54652, plain, (![B_1269]: (k9_subset_1(u1_struct_0('#skF_1'), B_1269, '#skF_3')=k3_xboole_0(B_1269, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_54638])).
% 42.26/31.36  tff(c_10, plain, (![A_6, B_7, C_8]: (m1_subset_1(k9_subset_1(A_6, B_7, C_8), k1_zfmisc_1(A_6)) | ~m1_subset_1(C_8, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 42.26/31.36  tff(c_54661, plain, (![B_1269]: (m1_subset_1(k3_xboole_0(B_1269, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_54652, c_10])).
% 42.26/31.36  tff(c_54669, plain, (![B_1269]: (m1_subset_1(k3_xboole_0(B_1269, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_54661])).
% 42.26/31.36  tff(c_54865, plain, (![B_2, B_1285]: (k9_subset_1(B_2, B_1285, B_2)=k3_xboole_0(B_1285, B_2))), inference(resolution, [status(thm)], [c_6, c_54845])).
% 42.26/31.36  tff(c_54770, plain, (![C_1278, A_1279, B_1280]: (v2_tex_2(C_1278, A_1279) | ~v2_tex_2(B_1280, A_1279) | ~r1_tarski(C_1278, B_1280) | ~m1_subset_1(C_1278, k1_zfmisc_1(u1_struct_0(A_1279))) | ~m1_subset_1(B_1280, k1_zfmisc_1(u1_struct_0(A_1279))) | ~l1_pre_topc(A_1279))), inference(cnfTransformation, [status(thm)], [f_63])).
% 42.26/31.36  tff(c_58346, plain, (![A_1403, B_1404, C_1405, A_1406]: (v2_tex_2(k9_subset_1(A_1403, B_1404, C_1405), A_1406) | ~v2_tex_2(A_1403, A_1406) | ~m1_subset_1(k9_subset_1(A_1403, B_1404, C_1405), k1_zfmisc_1(u1_struct_0(A_1406))) | ~m1_subset_1(A_1403, k1_zfmisc_1(u1_struct_0(A_1406))) | ~l1_pre_topc(A_1406) | ~m1_subset_1(C_1405, k1_zfmisc_1(A_1403)))), inference(resolution, [status(thm)], [c_54633, c_54770])).
% 42.26/31.36  tff(c_58388, plain, (![B_2, B_1285, A_1406]: (v2_tex_2(k9_subset_1(B_2, B_1285, B_2), A_1406) | ~v2_tex_2(B_2, A_1406) | ~m1_subset_1(k3_xboole_0(B_1285, B_2), k1_zfmisc_1(u1_struct_0(A_1406))) | ~m1_subset_1(B_2, k1_zfmisc_1(u1_struct_0(A_1406))) | ~l1_pre_topc(A_1406) | ~m1_subset_1(B_2, k1_zfmisc_1(B_2)))), inference(superposition, [status(thm), theory('equality')], [c_54865, c_58346])).
% 42.26/31.36  tff(c_105233, plain, (![B_2425, B_2426, A_2427]: (v2_tex_2(k3_xboole_0(B_2425, B_2426), A_2427) | ~v2_tex_2(B_2426, A_2427) | ~m1_subset_1(k3_xboole_0(B_2425, B_2426), k1_zfmisc_1(u1_struct_0(A_2427))) | ~m1_subset_1(B_2426, k1_zfmisc_1(u1_struct_0(A_2427))) | ~l1_pre_topc(A_2427) | ~m1_subset_1(B_2426, k1_zfmisc_1(B_2426)))), inference(demodulation, [status(thm), theory('equality')], [c_54865, c_58388])).
% 42.26/31.36  tff(c_105355, plain, (![B_1269]: (v2_tex_2(k3_xboole_0(B_1269, '#skF_3'), '#skF_1') | ~v2_tex_2('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_54669, c_105233])).
% 42.26/31.36  tff(c_105471, plain, (![B_2428]: (v2_tex_2(k3_xboole_0(B_2428, '#skF_3'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_55236, c_30, c_26, c_54589, c_105355])).
% 42.26/31.36  tff(c_105499, plain, (v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_54735, c_105471])).
% 42.26/31.36  tff(c_105501, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54755, c_105499])).
% 42.26/31.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 42.26/31.36  
% 42.26/31.36  Inference rules
% 42.26/31.36  ----------------------
% 42.26/31.36  #Ref     : 0
% 42.26/31.36  #Sup     : 28757
% 42.26/31.36  #Fact    : 0
% 42.26/31.36  #Define  : 0
% 42.26/31.36  #Split   : 23
% 42.26/31.36  #Chain   : 0
% 42.26/31.36  #Close   : 0
% 42.26/31.36  
% 42.26/31.36  Ordering : KBO
% 42.26/31.36  
% 42.26/31.36  Simplification rules
% 42.26/31.36  ----------------------
% 42.26/31.36  #Subsume      : 594
% 42.26/31.36  #Demod        : 12581
% 42.26/31.36  #Tautology    : 5524
% 42.26/31.36  #SimpNegUnit  : 2
% 42.26/31.36  #BackRed      : 5
% 42.26/31.36  
% 42.26/31.36  #Partial instantiations: 0
% 42.26/31.36  #Strategies tried      : 1
% 42.26/31.36  
% 42.26/31.36  Timing (in seconds)
% 42.26/31.36  ----------------------
% 42.26/31.37  Preprocessing        : 0.30
% 42.26/31.37  Parsing              : 0.17
% 42.26/31.37  CNF conversion       : 0.02
% 42.26/31.37  Main loop            : 30.25
% 42.26/31.37  Inferencing          : 4.14
% 42.26/31.37  Reduction            : 16.89
% 42.26/31.37  Demodulation         : 15.29
% 42.26/31.37  BG Simplification    : 0.68
% 42.26/31.37  Subsumption          : 6.86
% 42.26/31.37  Abstraction          : 0.90
% 42.26/31.37  MUC search           : 0.00
% 42.26/31.37  Cooper               : 0.00
% 42.26/31.37  Total                : 30.59
% 42.26/31.37  Index Insertion      : 0.00
% 42.26/31.37  Index Deletion       : 0.00
% 42.26/31.37  Index Matching       : 0.00
% 42.26/31.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------

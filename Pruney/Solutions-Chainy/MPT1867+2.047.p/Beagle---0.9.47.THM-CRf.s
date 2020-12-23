%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:28 EST 2020

% Result     : Theorem 5.24s
% Output     : CNFRefutation 5.24s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 263 expanded)
%              Number of leaves         :   33 ( 104 expanded)
%              Depth                    :   15
%              Number of atoms          :  145 ( 591 expanded)
%              Number of equality atoms :   39 ( 138 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_42,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_46,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_57,plain,(
    ! [A_50] :
      ( k1_xboole_0 = A_50
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_66,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_57])).

tff(c_18,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_69,plain,(
    ! [A_8] : r1_tarski('#skF_4',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_18])).

tff(c_14,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(A_4,B_5) = k1_xboole_0
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_86,plain,(
    ! [A_54,B_55] :
      ( k4_xboole_0(A_54,B_55) = '#skF_4'
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_14])).

tff(c_93,plain,(
    ! [A_8] : k4_xboole_0('#skF_4',A_8) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_69,c_86])).

tff(c_24,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_68,plain,(
    ! [A_14] : m1_subset_1('#skF_4',k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_24])).

tff(c_716,plain,(
    ! [A_104,B_105] :
      ( r1_tarski('#skF_2'(A_104,B_105),B_105)
      | v2_tex_2(B_105,A_104)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_721,plain,(
    ! [A_106] :
      ( r1_tarski('#skF_2'(A_106,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_106)
      | ~ l1_pre_topc(A_106) ) ),
    inference(resolution,[status(thm)],[c_68,c_716])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | k4_xboole_0(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_117,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | k4_xboole_0(A_4,B_5) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_12])).

tff(c_253,plain,(
    ! [B_68,A_69] :
      ( B_68 = A_69
      | ~ r1_tarski(B_68,A_69)
      | ~ r1_tarski(A_69,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_260,plain,(
    ! [B_5,A_4] :
      ( B_5 = A_4
      | ~ r1_tarski(B_5,A_4)
      | k4_xboole_0(A_4,B_5) != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_117,c_253])).

tff(c_724,plain,(
    ! [A_106] :
      ( '#skF_2'(A_106,'#skF_4') = '#skF_4'
      | k4_xboole_0('#skF_4','#skF_2'(A_106,'#skF_4')) != '#skF_4'
      | v2_tex_2('#skF_4',A_106)
      | ~ l1_pre_topc(A_106) ) ),
    inference(resolution,[status(thm)],[c_721,c_260])).

tff(c_747,plain,(
    ! [A_107] :
      ( '#skF_2'(A_107,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_107)
      | ~ l1_pre_topc(A_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_724])).

tff(c_750,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_747,c_42])).

tff(c_753,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_750])).

tff(c_50,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_764,plain,(
    ! [A_108,B_109] :
      ( m1_subset_1('#skF_2'(A_108,B_109),k1_zfmisc_1(u1_struct_0(A_108)))
      | v2_tex_2(B_109,A_108)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_28,plain,(
    ! [B_20,A_18] :
      ( v4_pre_topc(B_20,A_18)
      | ~ v1_xboole_0(B_20)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2363,plain,(
    ! [A_151,B_152] :
      ( v4_pre_topc('#skF_2'(A_151,B_152),A_151)
      | ~ v1_xboole_0('#skF_2'(A_151,B_152))
      | ~ v2_pre_topc(A_151)
      | v2_tex_2(B_152,A_151)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151) ) ),
    inference(resolution,[status(thm)],[c_764,c_28])).

tff(c_2615,plain,(
    ! [A_163] :
      ( v4_pre_topc('#skF_2'(A_163,'#skF_4'),A_163)
      | ~ v1_xboole_0('#skF_2'(A_163,'#skF_4'))
      | ~ v2_pre_topc(A_163)
      | v2_tex_2('#skF_4',A_163)
      | ~ l1_pre_topc(A_163) ) ),
    inference(resolution,[status(thm)],[c_68,c_2363])).

tff(c_2618,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_pre_topc('#skF_3')
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_753,c_2615])).

tff(c_2620,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_46,c_753,c_2618])).

tff(c_2621,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_2620])).

tff(c_10,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_94,plain,(
    ! [B_3] : k4_xboole_0(B_3,B_3) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10,c_86])).

tff(c_123,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(A_60,B_61) = A_60
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_135,plain,(
    ! [B_3] : k3_xboole_0(B_3,B_3) = B_3 ),
    inference(resolution,[status(thm)],[c_10,c_123])).

tff(c_162,plain,(
    ! [A_64,B_65] : k4_xboole_0(A_64,k4_xboole_0(A_64,B_65)) = k3_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_181,plain,(
    ! [B_3] : k4_xboole_0(B_3,'#skF_4') = k3_xboole_0(B_3,B_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_162])).

tff(c_195,plain,(
    ! [B_66] : k4_xboole_0(B_66,'#skF_4') = B_66 ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_181])).

tff(c_20,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_201,plain,(
    ! [B_66] : k4_xboole_0(B_66,B_66) = k3_xboole_0(B_66,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_20])).

tff(c_222,plain,(
    ! [B_66] : k3_xboole_0(B_66,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_201])).

tff(c_429,plain,(
    ! [A_86,B_87,C_88] :
      ( k9_subset_1(A_86,B_87,C_88) = k3_xboole_0(B_87,C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_431,plain,(
    ! [A_14,B_87] : k9_subset_1(A_14,B_87,'#skF_4') = k3_xboole_0(B_87,'#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_429])).

tff(c_433,plain,(
    ! [A_14,B_87] : k9_subset_1(A_14,B_87,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_431])).

tff(c_1384,plain,(
    ! [A_128,B_129,D_130] :
      ( k9_subset_1(u1_struct_0(A_128),B_129,D_130) != '#skF_2'(A_128,B_129)
      | ~ v4_pre_topc(D_130,A_128)
      | ~ m1_subset_1(D_130,k1_zfmisc_1(u1_struct_0(A_128)))
      | v2_tex_2(B_129,A_128)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1387,plain,(
    ! [A_128,B_87] :
      ( '#skF_2'(A_128,B_87) != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_128)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_128)))
      | v2_tex_2(B_87,A_128)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_1384])).

tff(c_5713,plain,(
    ! [A_208,B_209] :
      ( '#skF_2'(A_208,B_209) != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_208)
      | v2_tex_2(B_209,A_208)
      | ~ m1_subset_1(B_209,k1_zfmisc_1(u1_struct_0(A_208)))
      | ~ l1_pre_topc(A_208) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1387])).

tff(c_5727,plain,(
    ! [A_210] :
      ( '#skF_2'(A_210,'#skF_4') != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_210)
      | v2_tex_2('#skF_4',A_210)
      | ~ l1_pre_topc(A_210) ) ),
    inference(resolution,[status(thm)],[c_68,c_5713])).

tff(c_5730,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2621,c_5727])).

tff(c_5736,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_753,c_5730])).

tff(c_5738,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_5736])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:33:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.24/1.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.24/2.00  
% 5.24/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.24/2.00  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 5.24/2.00  
% 5.24/2.00  %Foreground sorts:
% 5.24/2.00  
% 5.24/2.00  
% 5.24/2.00  %Background operators:
% 5.24/2.00  
% 5.24/2.00  
% 5.24/2.00  %Foreground operators:
% 5.24/2.00  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.24/2.00  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.24/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.24/2.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.24/2.00  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.24/2.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.24/2.00  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.24/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.24/2.00  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 5.24/2.00  tff('#skF_3', type, '#skF_3': $i).
% 5.24/2.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.24/2.00  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.24/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.24/2.00  tff('#skF_4', type, '#skF_4': $i).
% 5.24/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.24/2.00  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.24/2.00  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.24/2.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.24/2.00  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.24/2.00  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.24/2.00  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.24/2.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.24/2.00  
% 5.24/2.01  tff(f_107, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 5.24/2.01  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.24/2.01  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.24/2.01  tff(f_40, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.24/2.01  tff(f_54, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.24/2.01  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tex_2)).
% 5.24/2.01  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.24/2.01  tff(f_71, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 5.24/2.01  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.24/2.01  tff(f_48, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.24/2.01  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 5.24/2.01  tff(c_42, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.24/2.01  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.24/2.01  tff(c_46, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.24/2.01  tff(c_57, plain, (![A_50]: (k1_xboole_0=A_50 | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_30])).
% 5.24/2.01  tff(c_66, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_46, c_57])).
% 5.24/2.01  tff(c_18, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.24/2.01  tff(c_69, plain, (![A_8]: (r1_tarski('#skF_4', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_18])).
% 5.24/2.01  tff(c_14, plain, (![A_4, B_5]: (k4_xboole_0(A_4, B_5)=k1_xboole_0 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.24/2.01  tff(c_86, plain, (![A_54, B_55]: (k4_xboole_0(A_54, B_55)='#skF_4' | ~r1_tarski(A_54, B_55))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_14])).
% 5.24/2.01  tff(c_93, plain, (![A_8]: (k4_xboole_0('#skF_4', A_8)='#skF_4')), inference(resolution, [status(thm)], [c_69, c_86])).
% 5.24/2.01  tff(c_24, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.24/2.01  tff(c_68, plain, (![A_14]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_24])).
% 5.24/2.01  tff(c_716, plain, (![A_104, B_105]: (r1_tarski('#skF_2'(A_104, B_105), B_105) | v2_tex_2(B_105, A_104) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.24/2.01  tff(c_721, plain, (![A_106]: (r1_tarski('#skF_2'(A_106, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_106) | ~l1_pre_topc(A_106))), inference(resolution, [status(thm)], [c_68, c_716])).
% 5.24/2.01  tff(c_12, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | k4_xboole_0(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.24/2.01  tff(c_117, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | k4_xboole_0(A_4, B_5)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_12])).
% 5.24/2.01  tff(c_253, plain, (![B_68, A_69]: (B_68=A_69 | ~r1_tarski(B_68, A_69) | ~r1_tarski(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.24/2.01  tff(c_260, plain, (![B_5, A_4]: (B_5=A_4 | ~r1_tarski(B_5, A_4) | k4_xboole_0(A_4, B_5)!='#skF_4')), inference(resolution, [status(thm)], [c_117, c_253])).
% 5.24/2.01  tff(c_724, plain, (![A_106]: ('#skF_2'(A_106, '#skF_4')='#skF_4' | k4_xboole_0('#skF_4', '#skF_2'(A_106, '#skF_4'))!='#skF_4' | v2_tex_2('#skF_4', A_106) | ~l1_pre_topc(A_106))), inference(resolution, [status(thm)], [c_721, c_260])).
% 5.24/2.01  tff(c_747, plain, (![A_107]: ('#skF_2'(A_107, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_107) | ~l1_pre_topc(A_107))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_724])).
% 5.24/2.01  tff(c_750, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_747, c_42])).
% 5.24/2.01  tff(c_753, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_750])).
% 5.24/2.01  tff(c_50, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.24/2.01  tff(c_764, plain, (![A_108, B_109]: (m1_subset_1('#skF_2'(A_108, B_109), k1_zfmisc_1(u1_struct_0(A_108))) | v2_tex_2(B_109, A_108) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.24/2.01  tff(c_28, plain, (![B_20, A_18]: (v4_pre_topc(B_20, A_18) | ~v1_xboole_0(B_20) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.24/2.01  tff(c_2363, plain, (![A_151, B_152]: (v4_pre_topc('#skF_2'(A_151, B_152), A_151) | ~v1_xboole_0('#skF_2'(A_151, B_152)) | ~v2_pre_topc(A_151) | v2_tex_2(B_152, A_151) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(A_151))) | ~l1_pre_topc(A_151))), inference(resolution, [status(thm)], [c_764, c_28])).
% 5.24/2.01  tff(c_2615, plain, (![A_163]: (v4_pre_topc('#skF_2'(A_163, '#skF_4'), A_163) | ~v1_xboole_0('#skF_2'(A_163, '#skF_4')) | ~v2_pre_topc(A_163) | v2_tex_2('#skF_4', A_163) | ~l1_pre_topc(A_163))), inference(resolution, [status(thm)], [c_68, c_2363])).
% 5.24/2.01  tff(c_2618, plain, (v4_pre_topc('#skF_4', '#skF_3') | ~v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_pre_topc('#skF_3') | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_753, c_2615])).
% 5.24/2.01  tff(c_2620, plain, (v4_pre_topc('#skF_4', '#skF_3') | v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_46, c_753, c_2618])).
% 5.24/2.01  tff(c_2621, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_42, c_2620])).
% 5.24/2.01  tff(c_10, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.24/2.01  tff(c_94, plain, (![B_3]: (k4_xboole_0(B_3, B_3)='#skF_4')), inference(resolution, [status(thm)], [c_10, c_86])).
% 5.24/2.01  tff(c_123, plain, (![A_60, B_61]: (k3_xboole_0(A_60, B_61)=A_60 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.24/2.01  tff(c_135, plain, (![B_3]: (k3_xboole_0(B_3, B_3)=B_3)), inference(resolution, [status(thm)], [c_10, c_123])).
% 5.24/2.01  tff(c_162, plain, (![A_64, B_65]: (k4_xboole_0(A_64, k4_xboole_0(A_64, B_65))=k3_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.24/2.01  tff(c_181, plain, (![B_3]: (k4_xboole_0(B_3, '#skF_4')=k3_xboole_0(B_3, B_3))), inference(superposition, [status(thm), theory('equality')], [c_94, c_162])).
% 5.24/2.01  tff(c_195, plain, (![B_66]: (k4_xboole_0(B_66, '#skF_4')=B_66)), inference(demodulation, [status(thm), theory('equality')], [c_135, c_181])).
% 5.24/2.01  tff(c_20, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.24/2.01  tff(c_201, plain, (![B_66]: (k4_xboole_0(B_66, B_66)=k3_xboole_0(B_66, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_195, c_20])).
% 5.24/2.01  tff(c_222, plain, (![B_66]: (k3_xboole_0(B_66, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_201])).
% 5.24/2.01  tff(c_429, plain, (![A_86, B_87, C_88]: (k9_subset_1(A_86, B_87, C_88)=k3_xboole_0(B_87, C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.24/2.01  tff(c_431, plain, (![A_14, B_87]: (k9_subset_1(A_14, B_87, '#skF_4')=k3_xboole_0(B_87, '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_429])).
% 5.24/2.01  tff(c_433, plain, (![A_14, B_87]: (k9_subset_1(A_14, B_87, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_222, c_431])).
% 5.24/2.01  tff(c_1384, plain, (![A_128, B_129, D_130]: (k9_subset_1(u1_struct_0(A_128), B_129, D_130)!='#skF_2'(A_128, B_129) | ~v4_pre_topc(D_130, A_128) | ~m1_subset_1(D_130, k1_zfmisc_1(u1_struct_0(A_128))) | v2_tex_2(B_129, A_128) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.24/2.01  tff(c_1387, plain, (![A_128, B_87]: ('#skF_2'(A_128, B_87)!='#skF_4' | ~v4_pre_topc('#skF_4', A_128) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_128))) | v2_tex_2(B_87, A_128) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(superposition, [status(thm), theory('equality')], [c_433, c_1384])).
% 5.24/2.01  tff(c_5713, plain, (![A_208, B_209]: ('#skF_2'(A_208, B_209)!='#skF_4' | ~v4_pre_topc('#skF_4', A_208) | v2_tex_2(B_209, A_208) | ~m1_subset_1(B_209, k1_zfmisc_1(u1_struct_0(A_208))) | ~l1_pre_topc(A_208))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1387])).
% 5.24/2.01  tff(c_5727, plain, (![A_210]: ('#skF_2'(A_210, '#skF_4')!='#skF_4' | ~v4_pre_topc('#skF_4', A_210) | v2_tex_2('#skF_4', A_210) | ~l1_pre_topc(A_210))), inference(resolution, [status(thm)], [c_68, c_5713])).
% 5.24/2.01  tff(c_5730, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2621, c_5727])).
% 5.24/2.01  tff(c_5736, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_753, c_5730])).
% 5.24/2.01  tff(c_5738, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_5736])).
% 5.24/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.24/2.01  
% 5.24/2.01  Inference rules
% 5.24/2.01  ----------------------
% 5.24/2.01  #Ref     : 0
% 5.24/2.01  #Sup     : 1313
% 5.24/2.01  #Fact    : 0
% 5.24/2.01  #Define  : 0
% 5.24/2.01  #Split   : 0
% 5.24/2.01  #Chain   : 0
% 5.24/2.01  #Close   : 0
% 5.24/2.01  
% 5.24/2.01  Ordering : KBO
% 5.24/2.01  
% 5.24/2.01  Simplification rules
% 5.24/2.01  ----------------------
% 5.24/2.02  #Subsume      : 239
% 5.24/2.02  #Demod        : 2233
% 5.24/2.02  #Tautology    : 852
% 5.24/2.02  #SimpNegUnit  : 10
% 5.24/2.02  #BackRed      : 4
% 5.24/2.02  
% 5.24/2.02  #Partial instantiations: 0
% 5.24/2.02  #Strategies tried      : 1
% 5.24/2.02  
% 5.24/2.02  Timing (in seconds)
% 5.24/2.02  ----------------------
% 5.24/2.02  Preprocessing        : 0.32
% 5.24/2.02  Parsing              : 0.17
% 5.24/2.02  CNF conversion       : 0.02
% 5.24/2.02  Main loop            : 0.93
% 5.24/2.02  Inferencing          : 0.30
% 5.24/2.02  Reduction            : 0.36
% 5.24/2.02  Demodulation         : 0.28
% 5.24/2.02  BG Simplification    : 0.04
% 5.24/2.02  Subsumption          : 0.18
% 5.24/2.02  Abstraction          : 0.06
% 5.24/2.02  MUC search           : 0.00
% 5.24/2.02  Cooper               : 0.00
% 5.24/2.02  Total                : 1.29
% 5.24/2.02  Index Insertion      : 0.00
% 5.24/2.02  Index Deletion       : 0.00
% 5.24/2.02  Index Matching       : 0.00
% 5.24/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------

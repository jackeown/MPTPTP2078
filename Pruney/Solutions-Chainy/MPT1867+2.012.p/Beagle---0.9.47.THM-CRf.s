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
% DateTime   : Thu Dec  3 10:29:24 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 3.94s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 177 expanded)
%              Number of leaves         :   34 (  75 expanded)
%              Depth                    :   17
%              Number of atoms          :  141 ( 363 expanded)
%              Number of equality atoms :   24 (  59 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_58,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_103,axiom,(
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
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_52,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_50,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_48,plain,(
    v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_57,plain,(
    ! [A_56] :
      ( k1_xboole_0 = A_56
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_61,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_48,c_57])).

tff(c_24,plain,(
    ! [A_19] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_67,plain,(
    ! [A_19] : m1_subset_1('#skF_6',k1_zfmisc_1(A_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_24])).

tff(c_313,plain,(
    ! [A_107,B_108] :
      ( r1_tarski('#skF_4'(A_107,B_108),B_108)
      | v2_tex_2(B_108,A_107)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_355,plain,(
    ! [A_114] :
      ( r1_tarski('#skF_4'(A_114,'#skF_6'),'#skF_6')
      | v2_tex_2('#skF_6',A_114)
      | ~ l1_pre_topc(A_114) ) ),
    inference(resolution,[status(thm)],[c_67,c_313])).

tff(c_90,plain,(
    ! [A_66,B_67] :
      ( r2_hidden('#skF_2'(A_66,B_67),A_66)
      | r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_101,plain,(
    ! [A_68,B_69] :
      ( ~ v1_xboole_0(A_68)
      | r1_tarski(A_68,B_69) ) ),
    inference(resolution,[status(thm)],[c_90,c_2])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | ~ r1_tarski(B_12,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_104,plain,(
    ! [B_69,A_68] :
      ( B_69 = A_68
      | ~ r1_tarski(B_69,A_68)
      | ~ v1_xboole_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_101,c_14])).

tff(c_367,plain,(
    ! [A_114] :
      ( '#skF_4'(A_114,'#skF_6') = '#skF_6'
      | ~ v1_xboole_0('#skF_6')
      | v2_tex_2('#skF_6',A_114)
      | ~ l1_pre_topc(A_114) ) ),
    inference(resolution,[status(thm)],[c_355,c_104])).

tff(c_389,plain,(
    ! [A_116] :
      ( '#skF_4'(A_116,'#skF_6') = '#skF_6'
      | v2_tex_2('#skF_6',A_116)
      | ~ l1_pre_topc(A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_367])).

tff(c_44,plain,(
    ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_392,plain,
    ( '#skF_4'('#skF_5','#skF_6') = '#skF_6'
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_389,c_44])).

tff(c_395,plain,(
    '#skF_4'('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_392])).

tff(c_273,plain,(
    ! [B_103,A_104] :
      ( v3_pre_topc(B_103,A_104)
      | ~ v1_xboole_0(B_103)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104)
      | ~ v2_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_285,plain,(
    ! [A_104] :
      ( v3_pre_topc('#skF_6',A_104)
      | ~ v1_xboole_0('#skF_6')
      | ~ l1_pre_topc(A_104)
      | ~ v2_pre_topc(A_104) ) ),
    inference(resolution,[status(thm)],[c_67,c_273])).

tff(c_290,plain,(
    ! [A_104] :
      ( v3_pre_topc('#skF_6',A_104)
      | ~ l1_pre_topc(A_104)
      | ~ v2_pre_topc(A_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_285])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_218,plain,(
    ! [A_91,B_92,C_93] :
      ( k9_subset_1(A_91,B_92,C_93) = k3_xboole_0(B_92,C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(A_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_221,plain,(
    ! [A_19,B_92] : k9_subset_1(A_19,B_92,'#skF_6') = k3_xboole_0(B_92,'#skF_6') ),
    inference(resolution,[status(thm)],[c_67,c_218])).

tff(c_231,plain,(
    ! [A_96,B_97,C_98] :
      ( m1_subset_1(k9_subset_1(A_96,B_97,C_98),k1_zfmisc_1(A_96))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_240,plain,(
    ! [B_92,A_19] :
      ( m1_subset_1(k3_xboole_0(B_92,'#skF_6'),k1_zfmisc_1(A_19))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_231])).

tff(c_246,plain,(
    ! [B_99,A_100] : m1_subset_1(k3_xboole_0(B_99,'#skF_6'),k1_zfmisc_1(A_100)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_240])).

tff(c_28,plain,(
    ! [C_25,B_24,A_23] :
      ( ~ v1_xboole_0(C_25)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(C_25))
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_255,plain,(
    ! [A_100,A_23,B_99] :
      ( ~ v1_xboole_0(A_100)
      | ~ r2_hidden(A_23,k3_xboole_0(B_99,'#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_246,c_28])).

tff(c_257,plain,(
    ! [A_101,B_102] : ~ r2_hidden(A_101,k3_xboole_0(B_102,'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_255])).

tff(c_291,plain,(
    ! [B_105] : v1_xboole_0(k3_xboole_0(B_105,'#skF_6')) ),
    inference(resolution,[status(thm)],[c_4,c_257])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_62,plain,(
    ! [A_10] :
      ( A_10 = '#skF_6'
      | ~ v1_xboole_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_12])).

tff(c_298,plain,(
    ! [B_105] : k3_xboole_0(B_105,'#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_291,c_62])).

tff(c_302,plain,(
    ! [A_19,B_92] : k9_subset_1(A_19,B_92,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_221])).

tff(c_519,plain,(
    ! [A_130,B_131,D_132] :
      ( k9_subset_1(u1_struct_0(A_130),B_131,D_132) != '#skF_4'(A_130,B_131)
      | ~ v3_pre_topc(D_132,A_130)
      | ~ m1_subset_1(D_132,k1_zfmisc_1(u1_struct_0(A_130)))
      | v2_tex_2(B_131,A_130)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_522,plain,(
    ! [A_130,B_92] :
      ( '#skF_4'(A_130,B_92) != '#skF_6'
      | ~ v3_pre_topc('#skF_6',A_130)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_130)))
      | v2_tex_2(B_92,A_130)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_519])).

tff(c_1331,plain,(
    ! [A_232,B_233] :
      ( '#skF_4'(A_232,B_233) != '#skF_6'
      | ~ v3_pre_topc('#skF_6',A_232)
      | v2_tex_2(B_233,A_232)
      | ~ m1_subset_1(B_233,k1_zfmisc_1(u1_struct_0(A_232)))
      | ~ l1_pre_topc(A_232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_522])).

tff(c_1359,plain,(
    ! [A_234] :
      ( '#skF_4'(A_234,'#skF_6') != '#skF_6'
      | ~ v3_pre_topc('#skF_6',A_234)
      | v2_tex_2('#skF_6',A_234)
      | ~ l1_pre_topc(A_234) ) ),
    inference(resolution,[status(thm)],[c_67,c_1331])).

tff(c_1432,plain,(
    ! [A_239] :
      ( '#skF_4'(A_239,'#skF_6') != '#skF_6'
      | v2_tex_2('#skF_6',A_239)
      | ~ l1_pre_topc(A_239)
      | ~ v2_pre_topc(A_239) ) ),
    inference(resolution,[status(thm)],[c_290,c_1359])).

tff(c_1435,plain,
    ( '#skF_4'('#skF_5','#skF_6') != '#skF_6'
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_1432,c_44])).

tff(c_1439,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_395,c_1435])).

tff(c_1440,plain,(
    ! [A_100] : ~ v1_xboole_0(A_100) ),
    inference(splitRight,[status(thm)],[c_255])).

tff(c_1446,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1440,c_48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:47:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.87/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.87/1.68  
% 3.87/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.87/1.68  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.87/1.68  
% 3.87/1.68  %Foreground sorts:
% 3.87/1.68  
% 3.87/1.68  
% 3.87/1.68  %Background operators:
% 3.87/1.68  
% 3.87/1.68  
% 3.87/1.68  %Foreground operators:
% 3.87/1.68  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.87/1.68  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.87/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.87/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.87/1.68  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.87/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.87/1.68  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.87/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.87/1.68  tff('#skF_5', type, '#skF_5': $i).
% 3.87/1.68  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.87/1.68  tff('#skF_6', type, '#skF_6': $i).
% 3.87/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.87/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.87/1.68  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.87/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.87/1.68  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.87/1.68  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.87/1.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.87/1.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.87/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.87/1.68  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.87/1.68  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.87/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.87/1.68  
% 3.94/1.70  tff(f_118, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 3.94/1.70  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.94/1.70  tff(f_58, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.94/1.70  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 3.94/1.70  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.94/1.70  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.94/1.70  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.94/1.70  tff(f_82, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tops_1)).
% 3.94/1.70  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.94/1.70  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 3.94/1.70  tff(f_71, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.94/1.70  tff(c_52, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.94/1.70  tff(c_50, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.94/1.70  tff(c_48, plain, (v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.94/1.70  tff(c_57, plain, (![A_56]: (k1_xboole_0=A_56 | ~v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.94/1.70  tff(c_61, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_48, c_57])).
% 3.94/1.70  tff(c_24, plain, (![A_19]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.94/1.70  tff(c_67, plain, (![A_19]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_24])).
% 3.94/1.70  tff(c_313, plain, (![A_107, B_108]: (r1_tarski('#skF_4'(A_107, B_108), B_108) | v2_tex_2(B_108, A_107) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.94/1.70  tff(c_355, plain, (![A_114]: (r1_tarski('#skF_4'(A_114, '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', A_114) | ~l1_pre_topc(A_114))), inference(resolution, [status(thm)], [c_67, c_313])).
% 3.94/1.70  tff(c_90, plain, (![A_66, B_67]: (r2_hidden('#skF_2'(A_66, B_67), A_66) | r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.94/1.70  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.94/1.70  tff(c_101, plain, (![A_68, B_69]: (~v1_xboole_0(A_68) | r1_tarski(A_68, B_69))), inference(resolution, [status(thm)], [c_90, c_2])).
% 3.94/1.70  tff(c_14, plain, (![B_12, A_11]: (B_12=A_11 | ~r1_tarski(B_12, A_11) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.94/1.70  tff(c_104, plain, (![B_69, A_68]: (B_69=A_68 | ~r1_tarski(B_69, A_68) | ~v1_xboole_0(A_68))), inference(resolution, [status(thm)], [c_101, c_14])).
% 3.94/1.70  tff(c_367, plain, (![A_114]: ('#skF_4'(A_114, '#skF_6')='#skF_6' | ~v1_xboole_0('#skF_6') | v2_tex_2('#skF_6', A_114) | ~l1_pre_topc(A_114))), inference(resolution, [status(thm)], [c_355, c_104])).
% 3.94/1.70  tff(c_389, plain, (![A_116]: ('#skF_4'(A_116, '#skF_6')='#skF_6' | v2_tex_2('#skF_6', A_116) | ~l1_pre_topc(A_116))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_367])).
% 3.94/1.70  tff(c_44, plain, (~v2_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.94/1.70  tff(c_392, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6' | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_389, c_44])).
% 3.94/1.70  tff(c_395, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_392])).
% 3.94/1.70  tff(c_273, plain, (![B_103, A_104]: (v3_pre_topc(B_103, A_104) | ~v1_xboole_0(B_103) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104) | ~v2_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.94/1.70  tff(c_285, plain, (![A_104]: (v3_pre_topc('#skF_6', A_104) | ~v1_xboole_0('#skF_6') | ~l1_pre_topc(A_104) | ~v2_pre_topc(A_104))), inference(resolution, [status(thm)], [c_67, c_273])).
% 3.94/1.70  tff(c_290, plain, (![A_104]: (v3_pre_topc('#skF_6', A_104) | ~l1_pre_topc(A_104) | ~v2_pre_topc(A_104))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_285])).
% 3.94/1.70  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.94/1.70  tff(c_218, plain, (![A_91, B_92, C_93]: (k9_subset_1(A_91, B_92, C_93)=k3_xboole_0(B_92, C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(A_91)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.94/1.70  tff(c_221, plain, (![A_19, B_92]: (k9_subset_1(A_19, B_92, '#skF_6')=k3_xboole_0(B_92, '#skF_6'))), inference(resolution, [status(thm)], [c_67, c_218])).
% 3.94/1.70  tff(c_231, plain, (![A_96, B_97, C_98]: (m1_subset_1(k9_subset_1(A_96, B_97, C_98), k1_zfmisc_1(A_96)) | ~m1_subset_1(C_98, k1_zfmisc_1(A_96)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.94/1.70  tff(c_240, plain, (![B_92, A_19]: (m1_subset_1(k3_xboole_0(B_92, '#skF_6'), k1_zfmisc_1(A_19)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_221, c_231])).
% 3.94/1.70  tff(c_246, plain, (![B_99, A_100]: (m1_subset_1(k3_xboole_0(B_99, '#skF_6'), k1_zfmisc_1(A_100)))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_240])).
% 3.94/1.70  tff(c_28, plain, (![C_25, B_24, A_23]: (~v1_xboole_0(C_25) | ~m1_subset_1(B_24, k1_zfmisc_1(C_25)) | ~r2_hidden(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.94/1.70  tff(c_255, plain, (![A_100, A_23, B_99]: (~v1_xboole_0(A_100) | ~r2_hidden(A_23, k3_xboole_0(B_99, '#skF_6')))), inference(resolution, [status(thm)], [c_246, c_28])).
% 3.94/1.70  tff(c_257, plain, (![A_101, B_102]: (~r2_hidden(A_101, k3_xboole_0(B_102, '#skF_6')))), inference(splitLeft, [status(thm)], [c_255])).
% 3.94/1.70  tff(c_291, plain, (![B_105]: (v1_xboole_0(k3_xboole_0(B_105, '#skF_6')))), inference(resolution, [status(thm)], [c_4, c_257])).
% 3.94/1.70  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.94/1.70  tff(c_62, plain, (![A_10]: (A_10='#skF_6' | ~v1_xboole_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_12])).
% 3.94/1.70  tff(c_298, plain, (![B_105]: (k3_xboole_0(B_105, '#skF_6')='#skF_6')), inference(resolution, [status(thm)], [c_291, c_62])).
% 3.94/1.70  tff(c_302, plain, (![A_19, B_92]: (k9_subset_1(A_19, B_92, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_298, c_221])).
% 3.94/1.70  tff(c_519, plain, (![A_130, B_131, D_132]: (k9_subset_1(u1_struct_0(A_130), B_131, D_132)!='#skF_4'(A_130, B_131) | ~v3_pre_topc(D_132, A_130) | ~m1_subset_1(D_132, k1_zfmisc_1(u1_struct_0(A_130))) | v2_tex_2(B_131, A_130) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.94/1.70  tff(c_522, plain, (![A_130, B_92]: ('#skF_4'(A_130, B_92)!='#skF_6' | ~v3_pre_topc('#skF_6', A_130) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_130))) | v2_tex_2(B_92, A_130) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130))), inference(superposition, [status(thm), theory('equality')], [c_302, c_519])).
% 3.94/1.70  tff(c_1331, plain, (![A_232, B_233]: ('#skF_4'(A_232, B_233)!='#skF_6' | ~v3_pre_topc('#skF_6', A_232) | v2_tex_2(B_233, A_232) | ~m1_subset_1(B_233, k1_zfmisc_1(u1_struct_0(A_232))) | ~l1_pre_topc(A_232))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_522])).
% 3.94/1.70  tff(c_1359, plain, (![A_234]: ('#skF_4'(A_234, '#skF_6')!='#skF_6' | ~v3_pre_topc('#skF_6', A_234) | v2_tex_2('#skF_6', A_234) | ~l1_pre_topc(A_234))), inference(resolution, [status(thm)], [c_67, c_1331])).
% 3.94/1.70  tff(c_1432, plain, (![A_239]: ('#skF_4'(A_239, '#skF_6')!='#skF_6' | v2_tex_2('#skF_6', A_239) | ~l1_pre_topc(A_239) | ~v2_pre_topc(A_239))), inference(resolution, [status(thm)], [c_290, c_1359])).
% 3.94/1.70  tff(c_1435, plain, ('#skF_4'('#skF_5', '#skF_6')!='#skF_6' | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_1432, c_44])).
% 3.94/1.70  tff(c_1439, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_395, c_1435])).
% 3.94/1.70  tff(c_1440, plain, (![A_100]: (~v1_xboole_0(A_100))), inference(splitRight, [status(thm)], [c_255])).
% 3.94/1.70  tff(c_1446, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1440, c_48])).
% 3.94/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.94/1.70  
% 3.94/1.70  Inference rules
% 3.94/1.70  ----------------------
% 3.94/1.70  #Ref     : 0
% 3.94/1.70  #Sup     : 316
% 3.94/1.70  #Fact    : 2
% 3.94/1.70  #Define  : 0
% 3.94/1.70  #Split   : 2
% 3.94/1.70  #Chain   : 0
% 3.94/1.70  #Close   : 0
% 3.94/1.70  
% 3.94/1.70  Ordering : KBO
% 3.94/1.70  
% 3.94/1.70  Simplification rules
% 3.94/1.70  ----------------------
% 3.94/1.70  #Subsume      : 101
% 3.94/1.70  #Demod        : 119
% 3.94/1.70  #Tautology    : 70
% 3.94/1.70  #SimpNegUnit  : 14
% 3.94/1.70  #BackRed      : 9
% 3.94/1.70  
% 3.94/1.70  #Partial instantiations: 0
% 3.94/1.70  #Strategies tried      : 1
% 3.94/1.70  
% 3.94/1.70  Timing (in seconds)
% 3.94/1.70  ----------------------
% 3.94/1.70  Preprocessing        : 0.35
% 3.94/1.70  Parsing              : 0.18
% 3.94/1.70  CNF conversion       : 0.03
% 3.94/1.70  Main loop            : 0.50
% 3.94/1.70  Inferencing          : 0.18
% 3.94/1.70  Reduction            : 0.14
% 3.94/1.70  Demodulation         : 0.10
% 3.94/1.70  BG Simplification    : 0.03
% 3.94/1.70  Subsumption          : 0.12
% 3.94/1.70  Abstraction          : 0.03
% 3.94/1.70  MUC search           : 0.00
% 3.94/1.70  Cooper               : 0.00
% 3.94/1.70  Total                : 0.89
% 3.94/1.70  Index Insertion      : 0.00
% 3.94/1.71  Index Deletion       : 0.00
% 3.94/1.71  Index Matching       : 0.00
% 3.94/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------

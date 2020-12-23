%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:14 EST 2020

% Result     : Theorem 4.51s
% Output     : CNFRefutation 4.51s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 276 expanded)
%              Number of leaves         :   27 ( 106 expanded)
%              Depth                    :   14
%              Number of atoms          :  278 ( 880 expanded)
%              Number of equality atoms :   42 ( 133 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tex_2(B,A)
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ~ ( r2_hidden(C,B)
                      & ! [D] :
                          ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                         => ~ ( v3_pre_topc(D,A)
                              & k9_subset_1(u1_struct_0(A),B,D) = k1_tarski(C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tex_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_76,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

tff(c_38,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(k1_tarski(A_5),B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [B_8,A_7] :
      ( m1_subset_1(k1_tarski(B_8),k1_zfmisc_1(A_7))
      | k1_xboole_0 = A_7
      | ~ m1_subset_1(B_8,A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_46,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_395,plain,(
    ! [A_105,B_106,C_107] :
      ( v3_pre_topc('#skF_1'(A_105,B_106,C_107),A_105)
      | ~ r1_tarski(C_107,B_106)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ v2_tex_2(B_106,A_105)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_405,plain,(
    ! [B_106] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_106,'#skF_4'),'#skF_3')
      | ~ r1_tarski('#skF_4',B_106)
      | ~ v2_tex_2(B_106,'#skF_3')
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_395])).

tff(c_412,plain,(
    ! [B_108] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_108,'#skF_4'),'#skF_3')
      | ~ r1_tarski('#skF_4',B_108)
      | ~ v2_tex_2(B_108,'#skF_3')
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_405])).

tff(c_431,plain,(
    ! [B_8] :
      ( v3_pre_topc('#skF_1'('#skF_3',k1_tarski(B_8),'#skF_4'),'#skF_3')
      | ~ r1_tarski('#skF_4',k1_tarski(B_8))
      | ~ v2_tex_2(k1_tarski(B_8),'#skF_3')
      | u1_struct_0('#skF_3') = k1_xboole_0
      | ~ m1_subset_1(B_8,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_16,c_412])).

tff(c_498,plain,(
    u1_struct_0('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_431])).

tff(c_69,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,B_57)
      | ~ m1_subset_1(A_56,k1_zfmisc_1(B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_73,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_69])).

tff(c_108,plain,(
    ! [B_67,A_68] :
      ( B_67 = A_68
      | ~ r1_tarski(B_67,A_68)
      | ~ r1_tarski(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_118,plain,
    ( u1_struct_0('#skF_3') = '#skF_4'
    | ~ r1_tarski(u1_struct_0('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_73,c_108])).

tff(c_143,plain,(
    ~ r1_tarski(u1_struct_0('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_509,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_143])).

tff(c_518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_509])).

tff(c_520,plain,(
    u1_struct_0('#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_431])).

tff(c_144,plain,(
    ! [B_71,A_72] :
      ( m1_subset_1(k1_tarski(B_71),k1_zfmisc_1(A_72))
      | k1_xboole_0 = A_72
      | ~ m1_subset_1(B_71,A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_152,plain,(
    ! [B_71,A_72] :
      ( r1_tarski(k1_tarski(B_71),A_72)
      | k1_xboole_0 = A_72
      | ~ m1_subset_1(B_71,A_72) ) ),
    inference(resolution,[status(thm)],[c_144,c_18])).

tff(c_554,plain,(
    ! [A_132,B_133,A_134] :
      ( v3_pre_topc('#skF_1'(A_132,B_133,A_134),A_132)
      | ~ r1_tarski(A_134,B_133)
      | ~ v2_tex_2(B_133,A_132)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132)
      | ~ r1_tarski(A_134,u1_struct_0(A_132)) ) ),
    inference(resolution,[status(thm)],[c_20,c_395])).

tff(c_570,plain,(
    ! [A_132,A_9,A_134] :
      ( v3_pre_topc('#skF_1'(A_132,A_9,A_134),A_132)
      | ~ r1_tarski(A_134,A_9)
      | ~ v2_tex_2(A_9,A_132)
      | ~ l1_pre_topc(A_132)
      | ~ r1_tarski(A_134,u1_struct_0(A_132))
      | ~ r1_tarski(A_9,u1_struct_0(A_132)) ) ),
    inference(resolution,[status(thm)],[c_20,c_554])).

tff(c_606,plain,(
    ! [A_148,B_149,C_150] :
      ( k9_subset_1(u1_struct_0(A_148),B_149,'#skF_1'(A_148,B_149,C_150)) = C_150
      | ~ r1_tarski(C_150,B_149)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ v2_tex_2(B_149,A_148)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ l1_pre_topc(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_724,plain,(
    ! [A_158,B_159,A_160] :
      ( k9_subset_1(u1_struct_0(A_158),B_159,'#skF_1'(A_158,B_159,A_160)) = A_160
      | ~ r1_tarski(A_160,B_159)
      | ~ v2_tex_2(B_159,A_158)
      | ~ m1_subset_1(B_159,k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ l1_pre_topc(A_158)
      | ~ r1_tarski(A_160,u1_struct_0(A_158)) ) ),
    inference(resolution,[status(thm)],[c_20,c_606])).

tff(c_736,plain,(
    ! [A_160] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3','#skF_4',A_160)) = A_160
      | ~ r1_tarski(A_160,'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_160,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_44,c_724])).

tff(c_744,plain,(
    ! [A_161] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3','#skF_4',A_161)) = A_161
      | ~ r1_tarski(A_161,'#skF_4')
      | ~ r1_tarski(A_161,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_736])).

tff(c_522,plain,(
    ! [A_129,B_130,C_131] :
      ( m1_subset_1('#skF_1'(A_129,B_130,C_131),k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ r1_tarski(C_131,B_130)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ v2_tex_2(B_130,A_129)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_36,plain,(
    ! [D_49] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',D_49) != k1_tarski('#skF_5')
      | ~ v3_pre_topc(D_49,'#skF_3')
      | ~ m1_subset_1(D_49,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_541,plain,(
    ! [B_130,C_131] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_130,C_131)) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_130,C_131),'#skF_3')
      | ~ r1_tarski(C_131,B_130)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_130,'#skF_3')
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_522,c_36])).

tff(c_553,plain,(
    ! [B_130,C_131] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_130,C_131)) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_130,C_131),'#skF_3')
      | ~ r1_tarski(C_131,B_130)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_130,'#skF_3')
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_541])).

tff(c_756,plain,(
    ! [A_161] :
      ( k1_tarski('#skF_5') != A_161
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',A_161),'#skF_3')
      | ~ r1_tarski(A_161,'#skF_4')
      | ~ m1_subset_1(A_161,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_161,'#skF_4')
      | ~ r1_tarski(A_161,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_744,c_553])).

tff(c_789,plain,(
    ! [A_165] :
      ( k1_tarski('#skF_5') != A_165
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',A_165),'#skF_3')
      | ~ m1_subset_1(A_165,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_165,'#skF_4')
      | ~ r1_tarski(A_165,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_756])).

tff(c_823,plain,(
    ! [A_166] :
      ( k1_tarski('#skF_5') != A_166
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',A_166),'#skF_3')
      | ~ r1_tarski(A_166,'#skF_4')
      | ~ r1_tarski(A_166,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_20,c_789])).

tff(c_831,plain,(
    ! [A_134] :
      ( k1_tarski('#skF_5') != A_134
      | ~ r1_tarski(A_134,'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_134,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_4',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_570,c_823])).

tff(c_857,plain,(
    ! [A_167] :
      ( k1_tarski('#skF_5') != A_167
      | ~ r1_tarski(A_167,'#skF_4')
      | ~ r1_tarski(A_167,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_46,c_42,c_831])).

tff(c_873,plain,(
    ! [B_71] :
      ( k1_tarski(B_71) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(B_71),'#skF_4')
      | u1_struct_0('#skF_3') = k1_xboole_0
      | ~ m1_subset_1(B_71,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_152,c_857])).

tff(c_915,plain,(
    ! [B_169] :
      ( k1_tarski(B_169) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(B_169),'#skF_4')
      | ~ m1_subset_1(B_169,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_520,c_873])).

tff(c_926,plain,(
    ! [A_170] :
      ( k1_tarski(A_170) != k1_tarski('#skF_5')
      | ~ m1_subset_1(A_170,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_170,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_14,c_915])).

tff(c_929,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_926])).

tff(c_933,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_929])).

tff(c_934,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_938,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_934,c_44])).

tff(c_1462,plain,(
    ! [A_248,B_249,C_250] :
      ( k9_subset_1(u1_struct_0(A_248),B_249,'#skF_1'(A_248,B_249,C_250)) = C_250
      | ~ r1_tarski(C_250,B_249)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(u1_struct_0(A_248)))
      | ~ v2_tex_2(B_249,A_248)
      | ~ m1_subset_1(B_249,k1_zfmisc_1(u1_struct_0(A_248)))
      | ~ l1_pre_topc(A_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1471,plain,(
    ! [B_249,C_250] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_249,'#skF_1'('#skF_3',B_249,C_250)) = C_250
      | ~ r1_tarski(C_250,B_249)
      | ~ m1_subset_1(C_250,k1_zfmisc_1('#skF_4'))
      | ~ v2_tex_2(B_249,'#skF_3')
      | ~ m1_subset_1(B_249,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_934,c_1462])).

tff(c_1494,plain,(
    ! [B_256,C_257] :
      ( k9_subset_1('#skF_4',B_256,'#skF_1'('#skF_3',B_256,C_257)) = C_257
      | ~ r1_tarski(C_257,B_256)
      | ~ m1_subset_1(C_257,k1_zfmisc_1('#skF_4'))
      | ~ v2_tex_2(B_256,'#skF_3')
      | ~ m1_subset_1(B_256,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_934,c_934,c_1471])).

tff(c_1721,plain,(
    ! [B_267,A_268] :
      ( k9_subset_1('#skF_4',B_267,'#skF_1'('#skF_3',B_267,A_268)) = A_268
      | ~ r1_tarski(A_268,B_267)
      | ~ v2_tex_2(B_267,'#skF_3')
      | ~ m1_subset_1(B_267,k1_zfmisc_1('#skF_4'))
      | ~ r1_tarski(A_268,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20,c_1494])).

tff(c_1745,plain,(
    ! [A_9,A_268] :
      ( k9_subset_1('#skF_4',A_9,'#skF_1'('#skF_3',A_9,A_268)) = A_268
      | ~ r1_tarski(A_268,A_9)
      | ~ v2_tex_2(A_9,'#skF_3')
      | ~ r1_tarski(A_268,'#skF_4')
      | ~ r1_tarski(A_9,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20,c_1721])).

tff(c_1378,plain,(
    ! [A_229,B_230,C_231] :
      ( m1_subset_1('#skF_1'(A_229,B_230,C_231),k1_zfmisc_1(u1_struct_0(A_229)))
      | ~ r1_tarski(C_231,B_230)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(u1_struct_0(A_229)))
      | ~ v2_tex_2(B_230,A_229)
      | ~ m1_subset_1(B_230,k1_zfmisc_1(u1_struct_0(A_229)))
      | ~ l1_pre_topc(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1388,plain,(
    ! [B_230,C_231] :
      ( m1_subset_1('#skF_1'('#skF_3',B_230,C_231),k1_zfmisc_1('#skF_4'))
      | ~ r1_tarski(C_231,B_230)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_230,'#skF_3')
      | ~ m1_subset_1(B_230,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_934,c_1378])).

tff(c_1416,plain,(
    ! [B_240,C_241] :
      ( m1_subset_1('#skF_1'('#skF_3',B_240,C_241),k1_zfmisc_1('#skF_4'))
      | ~ r1_tarski(C_241,B_240)
      | ~ m1_subset_1(C_241,k1_zfmisc_1('#skF_4'))
      | ~ v2_tex_2(B_240,'#skF_3')
      | ~ m1_subset_1(B_240,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_934,c_934,c_1388])).

tff(c_1425,plain,(
    ! [B_242,C_243] :
      ( r1_tarski('#skF_1'('#skF_3',B_242,C_243),'#skF_4')
      | ~ r1_tarski(C_243,B_242)
      | ~ m1_subset_1(C_243,k1_zfmisc_1('#skF_4'))
      | ~ v2_tex_2(B_242,'#skF_3')
      | ~ m1_subset_1(B_242,k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1416,c_18])).

tff(c_1234,plain,(
    ! [A_202,B_203,C_204] :
      ( v3_pre_topc('#skF_1'(A_202,B_203,C_204),A_202)
      | ~ r1_tarski(C_204,B_203)
      | ~ m1_subset_1(C_204,k1_zfmisc_1(u1_struct_0(A_202)))
      | ~ v2_tex_2(B_203,A_202)
      | ~ m1_subset_1(B_203,k1_zfmisc_1(u1_struct_0(A_202)))
      | ~ l1_pre_topc(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1241,plain,(
    ! [B_203,C_204] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_203,C_204),'#skF_3')
      | ~ r1_tarski(C_204,B_203)
      | ~ m1_subset_1(C_204,k1_zfmisc_1('#skF_4'))
      | ~ v2_tex_2(B_203,'#skF_3')
      | ~ m1_subset_1(B_203,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_934,c_1234])).

tff(c_1373,plain,(
    ! [B_227,C_228] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_227,C_228),'#skF_3')
      | ~ r1_tarski(C_228,B_227)
      | ~ m1_subset_1(C_228,k1_zfmisc_1('#skF_4'))
      | ~ v2_tex_2(B_227,'#skF_3')
      | ~ m1_subset_1(B_227,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_934,c_1241])).

tff(c_74,plain,(
    ! [A_58,B_59] :
      ( m1_subset_1(A_58,k1_zfmisc_1(B_59))
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_83,plain,(
    ! [A_58] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',A_58) != k1_tarski('#skF_5')
      | ~ v3_pre_topc(A_58,'#skF_3')
      | ~ r1_tarski(A_58,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_74,c_36])).

tff(c_1092,plain,(
    ! [A_58] :
      ( k9_subset_1('#skF_4','#skF_4',A_58) != k1_tarski('#skF_5')
      | ~ v3_pre_topc(A_58,'#skF_3')
      | ~ r1_tarski(A_58,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_934,c_934,c_83])).

tff(c_1377,plain,(
    ! [B_227,C_228] :
      ( k9_subset_1('#skF_4','#skF_4','#skF_1'('#skF_3',B_227,C_228)) != k1_tarski('#skF_5')
      | ~ r1_tarski('#skF_1'('#skF_3',B_227,C_228),'#skF_4')
      | ~ r1_tarski(C_228,B_227)
      | ~ m1_subset_1(C_228,k1_zfmisc_1('#skF_4'))
      | ~ v2_tex_2(B_227,'#skF_3')
      | ~ m1_subset_1(B_227,k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1373,c_1092])).

tff(c_1964,plain,(
    ! [B_280,C_281] :
      ( k9_subset_1('#skF_4','#skF_4','#skF_1'('#skF_3',B_280,C_281)) != k1_tarski('#skF_5')
      | ~ r1_tarski(C_281,B_280)
      | ~ m1_subset_1(C_281,k1_zfmisc_1('#skF_4'))
      | ~ v2_tex_2(B_280,'#skF_3')
      | ~ m1_subset_1(B_280,k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1425,c_1377])).

tff(c_1967,plain,(
    ! [A_268] :
      ( k1_tarski('#skF_5') != A_268
      | ~ r1_tarski(A_268,'#skF_4')
      | ~ m1_subset_1(A_268,k1_zfmisc_1('#skF_4'))
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
      | ~ r1_tarski(A_268,'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ r1_tarski(A_268,'#skF_4')
      | ~ r1_tarski('#skF_4','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1745,c_1964])).

tff(c_2012,plain,(
    ! [A_285] :
      ( k1_tarski('#skF_5') != A_285
      | ~ m1_subset_1(A_285,k1_zfmisc_1('#skF_4'))
      | ~ r1_tarski(A_285,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_42,c_938,c_42,c_1967])).

tff(c_2046,plain,(
    ! [A_286] :
      ( k1_tarski('#skF_5') != A_286
      | ~ r1_tarski(A_286,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20,c_2012])).

tff(c_2089,plain,(
    ! [A_287] :
      ( k1_tarski(A_287) != k1_tarski('#skF_5')
      | ~ r2_hidden(A_287,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_14,c_2046])).

tff(c_2101,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_38,c_2089])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:49:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.51/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.79  
% 4.51/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.79  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 4.51/1.79  
% 4.51/1.79  %Foreground sorts:
% 4.51/1.79  
% 4.51/1.79  
% 4.51/1.79  %Background operators:
% 4.51/1.79  
% 4.51/1.79  
% 4.51/1.79  %Foreground operators:
% 4.51/1.79  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.51/1.79  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.51/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.51/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.51/1.79  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.51/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.51/1.79  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.51/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.51/1.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.51/1.79  tff('#skF_5', type, '#skF_5': $i).
% 4.51/1.79  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.51/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.51/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.51/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.51/1.79  tff('#skF_4', type, '#skF_4': $i).
% 4.51/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.51/1.79  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.51/1.79  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.51/1.79  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.51/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.51/1.79  
% 4.51/1.81  tff(f_98, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_tex_2)).
% 4.51/1.81  tff(f_39, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.51/1.81  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.51/1.81  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.51/1.81  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.51/1.81  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 4.51/1.81  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 4.51/1.81  tff(c_38, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.51/1.81  tff(c_14, plain, (![A_5, B_6]: (r1_tarski(k1_tarski(A_5), B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.51/1.81  tff(c_20, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.51/1.81  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.51/1.81  tff(c_42, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.51/1.81  tff(c_40, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.51/1.81  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.51/1.81  tff(c_16, plain, (![B_8, A_7]: (m1_subset_1(k1_tarski(B_8), k1_zfmisc_1(A_7)) | k1_xboole_0=A_7 | ~m1_subset_1(B_8, A_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.51/1.81  tff(c_46, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.51/1.81  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.51/1.81  tff(c_395, plain, (![A_105, B_106, C_107]: (v3_pre_topc('#skF_1'(A_105, B_106, C_107), A_105) | ~r1_tarski(C_107, B_106) | ~m1_subset_1(C_107, k1_zfmisc_1(u1_struct_0(A_105))) | ~v2_tex_2(B_106, A_105) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.51/1.81  tff(c_405, plain, (![B_106]: (v3_pre_topc('#skF_1'('#skF_3', B_106, '#skF_4'), '#skF_3') | ~r1_tarski('#skF_4', B_106) | ~v2_tex_2(B_106, '#skF_3') | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_395])).
% 4.51/1.81  tff(c_412, plain, (![B_108]: (v3_pre_topc('#skF_1'('#skF_3', B_108, '#skF_4'), '#skF_3') | ~r1_tarski('#skF_4', B_108) | ~v2_tex_2(B_108, '#skF_3') | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_405])).
% 4.51/1.81  tff(c_431, plain, (![B_8]: (v3_pre_topc('#skF_1'('#skF_3', k1_tarski(B_8), '#skF_4'), '#skF_3') | ~r1_tarski('#skF_4', k1_tarski(B_8)) | ~v2_tex_2(k1_tarski(B_8), '#skF_3') | u1_struct_0('#skF_3')=k1_xboole_0 | ~m1_subset_1(B_8, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_16, c_412])).
% 4.51/1.81  tff(c_498, plain, (u1_struct_0('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_431])).
% 4.51/1.81  tff(c_69, plain, (![A_56, B_57]: (r1_tarski(A_56, B_57) | ~m1_subset_1(A_56, k1_zfmisc_1(B_57)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.51/1.81  tff(c_73, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_69])).
% 4.51/1.81  tff(c_108, plain, (![B_67, A_68]: (B_67=A_68 | ~r1_tarski(B_67, A_68) | ~r1_tarski(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.51/1.81  tff(c_118, plain, (u1_struct_0('#skF_3')='#skF_4' | ~r1_tarski(u1_struct_0('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_73, c_108])).
% 4.51/1.81  tff(c_143, plain, (~r1_tarski(u1_struct_0('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_118])).
% 4.51/1.81  tff(c_509, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_498, c_143])).
% 4.51/1.81  tff(c_518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_509])).
% 4.51/1.81  tff(c_520, plain, (u1_struct_0('#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_431])).
% 4.51/1.81  tff(c_144, plain, (![B_71, A_72]: (m1_subset_1(k1_tarski(B_71), k1_zfmisc_1(A_72)) | k1_xboole_0=A_72 | ~m1_subset_1(B_71, A_72))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.51/1.81  tff(c_18, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.51/1.81  tff(c_152, plain, (![B_71, A_72]: (r1_tarski(k1_tarski(B_71), A_72) | k1_xboole_0=A_72 | ~m1_subset_1(B_71, A_72))), inference(resolution, [status(thm)], [c_144, c_18])).
% 4.51/1.81  tff(c_554, plain, (![A_132, B_133, A_134]: (v3_pre_topc('#skF_1'(A_132, B_133, A_134), A_132) | ~r1_tarski(A_134, B_133) | ~v2_tex_2(B_133, A_132) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132) | ~r1_tarski(A_134, u1_struct_0(A_132)))), inference(resolution, [status(thm)], [c_20, c_395])).
% 4.51/1.81  tff(c_570, plain, (![A_132, A_9, A_134]: (v3_pre_topc('#skF_1'(A_132, A_9, A_134), A_132) | ~r1_tarski(A_134, A_9) | ~v2_tex_2(A_9, A_132) | ~l1_pre_topc(A_132) | ~r1_tarski(A_134, u1_struct_0(A_132)) | ~r1_tarski(A_9, u1_struct_0(A_132)))), inference(resolution, [status(thm)], [c_20, c_554])).
% 4.51/1.81  tff(c_606, plain, (![A_148, B_149, C_150]: (k9_subset_1(u1_struct_0(A_148), B_149, '#skF_1'(A_148, B_149, C_150))=C_150 | ~r1_tarski(C_150, B_149) | ~m1_subset_1(C_150, k1_zfmisc_1(u1_struct_0(A_148))) | ~v2_tex_2(B_149, A_148) | ~m1_subset_1(B_149, k1_zfmisc_1(u1_struct_0(A_148))) | ~l1_pre_topc(A_148))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.51/1.81  tff(c_724, plain, (![A_158, B_159, A_160]: (k9_subset_1(u1_struct_0(A_158), B_159, '#skF_1'(A_158, B_159, A_160))=A_160 | ~r1_tarski(A_160, B_159) | ~v2_tex_2(B_159, A_158) | ~m1_subset_1(B_159, k1_zfmisc_1(u1_struct_0(A_158))) | ~l1_pre_topc(A_158) | ~r1_tarski(A_160, u1_struct_0(A_158)))), inference(resolution, [status(thm)], [c_20, c_606])).
% 4.51/1.81  tff(c_736, plain, (![A_160]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', '#skF_4', A_160))=A_160 | ~r1_tarski(A_160, '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_160, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_44, c_724])).
% 4.51/1.81  tff(c_744, plain, (![A_161]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', '#skF_4', A_161))=A_161 | ~r1_tarski(A_161, '#skF_4') | ~r1_tarski(A_161, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_736])).
% 4.51/1.81  tff(c_522, plain, (![A_129, B_130, C_131]: (m1_subset_1('#skF_1'(A_129, B_130, C_131), k1_zfmisc_1(u1_struct_0(A_129))) | ~r1_tarski(C_131, B_130) | ~m1_subset_1(C_131, k1_zfmisc_1(u1_struct_0(A_129))) | ~v2_tex_2(B_130, A_129) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.51/1.81  tff(c_36, plain, (![D_49]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', D_49)!=k1_tarski('#skF_5') | ~v3_pre_topc(D_49, '#skF_3') | ~m1_subset_1(D_49, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.51/1.81  tff(c_541, plain, (![B_130, C_131]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_130, C_131))!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', B_130, C_131), '#skF_3') | ~r1_tarski(C_131, B_130) | ~m1_subset_1(C_131, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_130, '#skF_3') | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_522, c_36])).
% 4.51/1.81  tff(c_553, plain, (![B_130, C_131]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_130, C_131))!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', B_130, C_131), '#skF_3') | ~r1_tarski(C_131, B_130) | ~m1_subset_1(C_131, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_130, '#skF_3') | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_541])).
% 4.51/1.81  tff(c_756, plain, (![A_161]: (k1_tarski('#skF_5')!=A_161 | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', A_161), '#skF_3') | ~r1_tarski(A_161, '#skF_4') | ~m1_subset_1(A_161, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_161, '#skF_4') | ~r1_tarski(A_161, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_744, c_553])).
% 4.51/1.81  tff(c_789, plain, (![A_165]: (k1_tarski('#skF_5')!=A_165 | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', A_165), '#skF_3') | ~m1_subset_1(A_165, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_165, '#skF_4') | ~r1_tarski(A_165, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_756])).
% 4.51/1.81  tff(c_823, plain, (![A_166]: (k1_tarski('#skF_5')!=A_166 | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', A_166), '#skF_3') | ~r1_tarski(A_166, '#skF_4') | ~r1_tarski(A_166, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_20, c_789])).
% 4.51/1.81  tff(c_831, plain, (![A_134]: (k1_tarski('#skF_5')!=A_134 | ~r1_tarski(A_134, '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_134, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_4', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_570, c_823])).
% 4.51/1.81  tff(c_857, plain, (![A_167]: (k1_tarski('#skF_5')!=A_167 | ~r1_tarski(A_167, '#skF_4') | ~r1_tarski(A_167, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_46, c_42, c_831])).
% 4.51/1.81  tff(c_873, plain, (![B_71]: (k1_tarski(B_71)!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(B_71), '#skF_4') | u1_struct_0('#skF_3')=k1_xboole_0 | ~m1_subset_1(B_71, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_152, c_857])).
% 4.51/1.81  tff(c_915, plain, (![B_169]: (k1_tarski(B_169)!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(B_169), '#skF_4') | ~m1_subset_1(B_169, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_520, c_873])).
% 4.51/1.81  tff(c_926, plain, (![A_170]: (k1_tarski(A_170)!=k1_tarski('#skF_5') | ~m1_subset_1(A_170, u1_struct_0('#skF_3')) | ~r2_hidden(A_170, '#skF_4'))), inference(resolution, [status(thm)], [c_14, c_915])).
% 4.51/1.81  tff(c_929, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_926])).
% 4.51/1.81  tff(c_933, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_929])).
% 4.51/1.81  tff(c_934, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_118])).
% 4.51/1.81  tff(c_938, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_934, c_44])).
% 4.51/1.81  tff(c_1462, plain, (![A_248, B_249, C_250]: (k9_subset_1(u1_struct_0(A_248), B_249, '#skF_1'(A_248, B_249, C_250))=C_250 | ~r1_tarski(C_250, B_249) | ~m1_subset_1(C_250, k1_zfmisc_1(u1_struct_0(A_248))) | ~v2_tex_2(B_249, A_248) | ~m1_subset_1(B_249, k1_zfmisc_1(u1_struct_0(A_248))) | ~l1_pre_topc(A_248))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.51/1.81  tff(c_1471, plain, (![B_249, C_250]: (k9_subset_1(u1_struct_0('#skF_3'), B_249, '#skF_1'('#skF_3', B_249, C_250))=C_250 | ~r1_tarski(C_250, B_249) | ~m1_subset_1(C_250, k1_zfmisc_1('#skF_4')) | ~v2_tex_2(B_249, '#skF_3') | ~m1_subset_1(B_249, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_934, c_1462])).
% 4.51/1.81  tff(c_1494, plain, (![B_256, C_257]: (k9_subset_1('#skF_4', B_256, '#skF_1'('#skF_3', B_256, C_257))=C_257 | ~r1_tarski(C_257, B_256) | ~m1_subset_1(C_257, k1_zfmisc_1('#skF_4')) | ~v2_tex_2(B_256, '#skF_3') | ~m1_subset_1(B_256, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_934, c_934, c_1471])).
% 4.51/1.81  tff(c_1721, plain, (![B_267, A_268]: (k9_subset_1('#skF_4', B_267, '#skF_1'('#skF_3', B_267, A_268))=A_268 | ~r1_tarski(A_268, B_267) | ~v2_tex_2(B_267, '#skF_3') | ~m1_subset_1(B_267, k1_zfmisc_1('#skF_4')) | ~r1_tarski(A_268, '#skF_4'))), inference(resolution, [status(thm)], [c_20, c_1494])).
% 4.51/1.81  tff(c_1745, plain, (![A_9, A_268]: (k9_subset_1('#skF_4', A_9, '#skF_1'('#skF_3', A_9, A_268))=A_268 | ~r1_tarski(A_268, A_9) | ~v2_tex_2(A_9, '#skF_3') | ~r1_tarski(A_268, '#skF_4') | ~r1_tarski(A_9, '#skF_4'))), inference(resolution, [status(thm)], [c_20, c_1721])).
% 4.51/1.81  tff(c_1378, plain, (![A_229, B_230, C_231]: (m1_subset_1('#skF_1'(A_229, B_230, C_231), k1_zfmisc_1(u1_struct_0(A_229))) | ~r1_tarski(C_231, B_230) | ~m1_subset_1(C_231, k1_zfmisc_1(u1_struct_0(A_229))) | ~v2_tex_2(B_230, A_229) | ~m1_subset_1(B_230, k1_zfmisc_1(u1_struct_0(A_229))) | ~l1_pre_topc(A_229))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.51/1.81  tff(c_1388, plain, (![B_230, C_231]: (m1_subset_1('#skF_1'('#skF_3', B_230, C_231), k1_zfmisc_1('#skF_4')) | ~r1_tarski(C_231, B_230) | ~m1_subset_1(C_231, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_230, '#skF_3') | ~m1_subset_1(B_230, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_934, c_1378])).
% 4.51/1.81  tff(c_1416, plain, (![B_240, C_241]: (m1_subset_1('#skF_1'('#skF_3', B_240, C_241), k1_zfmisc_1('#skF_4')) | ~r1_tarski(C_241, B_240) | ~m1_subset_1(C_241, k1_zfmisc_1('#skF_4')) | ~v2_tex_2(B_240, '#skF_3') | ~m1_subset_1(B_240, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_934, c_934, c_1388])).
% 4.51/1.81  tff(c_1425, plain, (![B_242, C_243]: (r1_tarski('#skF_1'('#skF_3', B_242, C_243), '#skF_4') | ~r1_tarski(C_243, B_242) | ~m1_subset_1(C_243, k1_zfmisc_1('#skF_4')) | ~v2_tex_2(B_242, '#skF_3') | ~m1_subset_1(B_242, k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_1416, c_18])).
% 4.51/1.81  tff(c_1234, plain, (![A_202, B_203, C_204]: (v3_pre_topc('#skF_1'(A_202, B_203, C_204), A_202) | ~r1_tarski(C_204, B_203) | ~m1_subset_1(C_204, k1_zfmisc_1(u1_struct_0(A_202))) | ~v2_tex_2(B_203, A_202) | ~m1_subset_1(B_203, k1_zfmisc_1(u1_struct_0(A_202))) | ~l1_pre_topc(A_202))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.51/1.81  tff(c_1241, plain, (![B_203, C_204]: (v3_pre_topc('#skF_1'('#skF_3', B_203, C_204), '#skF_3') | ~r1_tarski(C_204, B_203) | ~m1_subset_1(C_204, k1_zfmisc_1('#skF_4')) | ~v2_tex_2(B_203, '#skF_3') | ~m1_subset_1(B_203, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_934, c_1234])).
% 4.51/1.81  tff(c_1373, plain, (![B_227, C_228]: (v3_pre_topc('#skF_1'('#skF_3', B_227, C_228), '#skF_3') | ~r1_tarski(C_228, B_227) | ~m1_subset_1(C_228, k1_zfmisc_1('#skF_4')) | ~v2_tex_2(B_227, '#skF_3') | ~m1_subset_1(B_227, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_934, c_1241])).
% 4.51/1.81  tff(c_74, plain, (![A_58, B_59]: (m1_subset_1(A_58, k1_zfmisc_1(B_59)) | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.51/1.81  tff(c_83, plain, (![A_58]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', A_58)!=k1_tarski('#skF_5') | ~v3_pre_topc(A_58, '#skF_3') | ~r1_tarski(A_58, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_74, c_36])).
% 4.51/1.81  tff(c_1092, plain, (![A_58]: (k9_subset_1('#skF_4', '#skF_4', A_58)!=k1_tarski('#skF_5') | ~v3_pre_topc(A_58, '#skF_3') | ~r1_tarski(A_58, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_934, c_934, c_83])).
% 4.51/1.81  tff(c_1377, plain, (![B_227, C_228]: (k9_subset_1('#skF_4', '#skF_4', '#skF_1'('#skF_3', B_227, C_228))!=k1_tarski('#skF_5') | ~r1_tarski('#skF_1'('#skF_3', B_227, C_228), '#skF_4') | ~r1_tarski(C_228, B_227) | ~m1_subset_1(C_228, k1_zfmisc_1('#skF_4')) | ~v2_tex_2(B_227, '#skF_3') | ~m1_subset_1(B_227, k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_1373, c_1092])).
% 4.51/1.81  tff(c_1964, plain, (![B_280, C_281]: (k9_subset_1('#skF_4', '#skF_4', '#skF_1'('#skF_3', B_280, C_281))!=k1_tarski('#skF_5') | ~r1_tarski(C_281, B_280) | ~m1_subset_1(C_281, k1_zfmisc_1('#skF_4')) | ~v2_tex_2(B_280, '#skF_3') | ~m1_subset_1(B_280, k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_1425, c_1377])).
% 4.51/1.81  tff(c_1967, plain, (![A_268]: (k1_tarski('#skF_5')!=A_268 | ~r1_tarski(A_268, '#skF_4') | ~m1_subset_1(A_268, k1_zfmisc_1('#skF_4')) | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~r1_tarski(A_268, '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~r1_tarski(A_268, '#skF_4') | ~r1_tarski('#skF_4', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1745, c_1964])).
% 4.51/1.81  tff(c_2012, plain, (![A_285]: (k1_tarski('#skF_5')!=A_285 | ~m1_subset_1(A_285, k1_zfmisc_1('#skF_4')) | ~r1_tarski(A_285, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_42, c_938, c_42, c_1967])).
% 4.51/1.81  tff(c_2046, plain, (![A_286]: (k1_tarski('#skF_5')!=A_286 | ~r1_tarski(A_286, '#skF_4'))), inference(resolution, [status(thm)], [c_20, c_2012])).
% 4.51/1.81  tff(c_2089, plain, (![A_287]: (k1_tarski(A_287)!=k1_tarski('#skF_5') | ~r2_hidden(A_287, '#skF_4'))), inference(resolution, [status(thm)], [c_14, c_2046])).
% 4.51/1.81  tff(c_2101, plain, $false, inference(resolution, [status(thm)], [c_38, c_2089])).
% 4.51/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.81  
% 4.51/1.81  Inference rules
% 4.51/1.81  ----------------------
% 4.51/1.81  #Ref     : 0
% 4.51/1.81  #Sup     : 396
% 4.51/1.81  #Fact    : 0
% 4.51/1.81  #Define  : 0
% 4.51/1.81  #Split   : 13
% 4.51/1.81  #Chain   : 0
% 4.51/1.81  #Close   : 0
% 4.51/1.81  
% 4.51/1.81  Ordering : KBO
% 4.51/1.81  
% 4.51/1.81  Simplification rules
% 4.51/1.81  ----------------------
% 4.51/1.81  #Subsume      : 53
% 4.51/1.81  #Demod        : 384
% 4.51/1.81  #Tautology    : 126
% 4.51/1.81  #SimpNegUnit  : 12
% 4.51/1.81  #BackRed      : 46
% 4.51/1.81  
% 4.51/1.81  #Partial instantiations: 0
% 4.51/1.81  #Strategies tried      : 1
% 4.51/1.81  
% 4.51/1.81  Timing (in seconds)
% 4.51/1.81  ----------------------
% 4.51/1.81  Preprocessing        : 0.33
% 4.51/1.81  Parsing              : 0.17
% 4.51/1.81  CNF conversion       : 0.02
% 4.51/1.81  Main loop            : 0.72
% 4.51/1.81  Inferencing          : 0.26
% 4.51/1.81  Reduction            : 0.21
% 4.51/1.81  Demodulation         : 0.15
% 4.51/1.81  BG Simplification    : 0.03
% 4.51/1.81  Subsumption          : 0.16
% 4.51/1.81  Abstraction          : 0.04
% 4.51/1.81  MUC search           : 0.00
% 4.51/1.81  Cooper               : 0.00
% 4.51/1.81  Total                : 1.09
% 4.51/1.81  Index Insertion      : 0.00
% 4.51/1.81  Index Deletion       : 0.00
% 4.51/1.81  Index Matching       : 0.00
% 4.51/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------

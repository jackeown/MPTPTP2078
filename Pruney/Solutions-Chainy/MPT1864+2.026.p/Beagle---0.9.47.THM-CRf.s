%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:17 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 110 expanded)
%              Number of leaves         :   27 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :  158 ( 337 expanded)
%              Number of equality atoms :   19 (  37 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
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

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_71,axiom,(
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

tff(c_32,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_87,plain,(
    ! [A_68,B_69,C_70] :
      ( r1_tarski(k2_tarski(A_68,B_69),C_70)
      | ~ r2_hidden(B_69,C_70)
      | ~ r2_hidden(A_68,C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_96,plain,(
    ! [A_1,C_70] :
      ( r1_tarski(k1_tarski(A_1),C_70)
      | ~ r2_hidden(A_1,C_70)
      | ~ r2_hidden(A_1,C_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_87])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_80,plain,(
    ! [C_65,B_66,A_67] :
      ( ~ v1_xboole_0(C_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(C_65))
      | ~ r2_hidden(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_86,plain,(
    ! [A_67] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_67,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_80])).

tff(c_99,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_50,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(A_50,B_51)
      | ~ m1_subset_1(A_50,k1_zfmisc_1(B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_54,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_50])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_36,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_208,plain,(
    ! [A_105,B_106,C_107] :
      ( v3_pre_topc('#skF_1'(A_105,B_106,C_107),A_105)
      | ~ r1_tarski(C_107,B_106)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ v2_tex_2(B_106,A_105)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_313,plain,(
    ! [A_121,B_122,A_123] :
      ( v3_pre_topc('#skF_1'(A_121,B_122,A_123),A_121)
      | ~ r1_tarski(A_123,B_122)
      | ~ v2_tex_2(B_122,A_121)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121)
      | ~ r1_tarski(A_123,u1_struct_0(A_121)) ) ),
    inference(resolution,[status(thm)],[c_14,c_208])).

tff(c_325,plain,(
    ! [A_121,A_7,A_123] :
      ( v3_pre_topc('#skF_1'(A_121,A_7,A_123),A_121)
      | ~ r1_tarski(A_123,A_7)
      | ~ v2_tex_2(A_7,A_121)
      | ~ l1_pre_topc(A_121)
      | ~ r1_tarski(A_123,u1_struct_0(A_121))
      | ~ r1_tarski(A_7,u1_struct_0(A_121)) ) ),
    inference(resolution,[status(thm)],[c_14,c_313])).

tff(c_349,plain,(
    ! [A_138,B_139,C_140] :
      ( k9_subset_1(u1_struct_0(A_138),B_139,'#skF_1'(A_138,B_139,C_140)) = C_140
      | ~ r1_tarski(C_140,B_139)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ v2_tex_2(B_139,A_138)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_pre_topc(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_400,plain,(
    ! [A_143,B_144,A_145] :
      ( k9_subset_1(u1_struct_0(A_143),B_144,'#skF_1'(A_143,B_144,A_145)) = A_145
      | ~ r1_tarski(A_145,B_144)
      | ~ v2_tex_2(B_144,A_143)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143)
      | ~ r1_tarski(A_145,u1_struct_0(A_143)) ) ),
    inference(resolution,[status(thm)],[c_14,c_349])).

tff(c_412,plain,(
    ! [A_143,A_7,A_145] :
      ( k9_subset_1(u1_struct_0(A_143),A_7,'#skF_1'(A_143,A_7,A_145)) = A_145
      | ~ r1_tarski(A_145,A_7)
      | ~ v2_tex_2(A_7,A_143)
      | ~ l1_pre_topc(A_143)
      | ~ r1_tarski(A_145,u1_struct_0(A_143))
      | ~ r1_tarski(A_7,u1_struct_0(A_143)) ) ),
    inference(resolution,[status(thm)],[c_14,c_400])).

tff(c_275,plain,(
    ! [A_118,B_119,C_120] :
      ( m1_subset_1('#skF_1'(A_118,B_119,C_120),k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ r1_tarski(C_120,B_119)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ v2_tex_2(B_119,A_118)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_30,plain,(
    ! [D_48] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',D_48) != k1_tarski('#skF_5')
      | ~ v3_pre_topc(D_48,'#skF_3')
      | ~ m1_subset_1(D_48,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_295,plain,(
    ! [B_119,C_120] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_119,C_120)) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_119,C_120),'#skF_3')
      | ~ r1_tarski(C_120,B_119)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_119,'#skF_3')
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_275,c_30])).

tff(c_518,plain,(
    ! [B_159,C_160] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_159,C_160)) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_159,C_160),'#skF_3')
      | ~ r1_tarski(C_160,B_159)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_159,'#skF_3')
      | ~ m1_subset_1(B_159,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_295])).

tff(c_521,plain,(
    ! [A_145] :
      ( k1_tarski('#skF_5') != A_145
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',A_145),'#skF_3')
      | ~ r1_tarski(A_145,'#skF_4')
      | ~ m1_subset_1(A_145,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_145,'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_145,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_4',u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_518])).

tff(c_534,plain,(
    ! [A_161] :
      ( k1_tarski('#skF_5') != A_161
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',A_161),'#skF_3')
      | ~ m1_subset_1(A_161,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_161,'#skF_4')
      | ~ r1_tarski(A_161,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_40,c_36,c_38,c_36,c_521])).

tff(c_561,plain,(
    ! [A_162] :
      ( k1_tarski('#skF_5') != A_162
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',A_162),'#skF_3')
      | ~ r1_tarski(A_162,'#skF_4')
      | ~ r1_tarski(A_162,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_14,c_534])).

tff(c_569,plain,(
    ! [A_123] :
      ( k1_tarski('#skF_5') != A_123
      | ~ r1_tarski(A_123,'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_123,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_4',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_325,c_561])).

tff(c_588,plain,(
    ! [A_163] :
      ( k1_tarski('#skF_5') != A_163
      | ~ r1_tarski(A_163,'#skF_4')
      | ~ r1_tarski(A_163,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_40,c_36,c_569])).

tff(c_622,plain,(
    ! [A_164] :
      ( k1_tarski(A_164) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_164),'#skF_4')
      | ~ r2_hidden(A_164,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_96,c_588])).

tff(c_626,plain,(
    ! [A_5] :
      ( k1_tarski(A_5) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_5),'#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_5,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_10,c_622])).

tff(c_630,plain,(
    ! [A_165] :
      ( k1_tarski(A_165) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_165),'#skF_4')
      | ~ m1_subset_1(A_165,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_626])).

tff(c_636,plain,(
    ! [A_166] :
      ( k1_tarski(A_166) != k1_tarski('#skF_5')
      | ~ m1_subset_1(A_166,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_166,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_96,c_630])).

tff(c_639,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_636])).

tff(c_643,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_639])).

tff(c_644,plain,(
    ! [A_67] : ~ r2_hidden(A_67,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_647,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_644,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:03:05 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.82/2.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/2.03  
% 3.82/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/2.03  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.82/2.03  
% 3.82/2.03  %Foreground sorts:
% 3.82/2.03  
% 3.82/2.03  
% 3.82/2.03  %Background operators:
% 3.82/2.03  
% 3.82/2.03  
% 3.82/2.03  %Foreground operators:
% 3.82/2.03  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.82/2.03  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.82/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.82/2.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.82/2.03  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.82/2.03  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.82/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.82/2.03  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.82/2.03  tff('#skF_5', type, '#skF_5': $i).
% 3.82/2.03  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.82/2.03  tff('#skF_3', type, '#skF_3': $i).
% 3.82/2.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.82/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.82/2.03  tff('#skF_4', type, '#skF_4': $i).
% 3.82/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.82/2.03  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.82/2.03  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.82/2.03  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.82/2.03  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.82/2.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.82/2.03  
% 3.82/2.05  tff(f_93, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_tex_2)).
% 3.82/2.05  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.82/2.05  tff(f_33, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.82/2.05  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.82/2.05  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.82/2.05  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.82/2.05  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 3.82/2.05  tff(c_32, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.82/2.05  tff(c_34, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.82/2.05  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.82/2.05  tff(c_87, plain, (![A_68, B_69, C_70]: (r1_tarski(k2_tarski(A_68, B_69), C_70) | ~r2_hidden(B_69, C_70) | ~r2_hidden(A_68, C_70))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.82/2.05  tff(c_96, plain, (![A_1, C_70]: (r1_tarski(k1_tarski(A_1), C_70) | ~r2_hidden(A_1, C_70) | ~r2_hidden(A_1, C_70))), inference(superposition, [status(thm), theory('equality')], [c_2, c_87])).
% 3.82/2.05  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.82/2.05  tff(c_80, plain, (![C_65, B_66, A_67]: (~v1_xboole_0(C_65) | ~m1_subset_1(B_66, k1_zfmisc_1(C_65)) | ~r2_hidden(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.82/2.05  tff(c_86, plain, (![A_67]: (~v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden(A_67, '#skF_4'))), inference(resolution, [status(thm)], [c_38, c_80])).
% 3.82/2.05  tff(c_99, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_86])).
% 3.82/2.05  tff(c_10, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.82/2.05  tff(c_50, plain, (![A_50, B_51]: (r1_tarski(A_50, B_51) | ~m1_subset_1(A_50, k1_zfmisc_1(B_51)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.82/2.05  tff(c_54, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_50])).
% 3.82/2.05  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.82/2.05  tff(c_36, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.82/2.05  tff(c_14, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.82/2.05  tff(c_208, plain, (![A_105, B_106, C_107]: (v3_pre_topc('#skF_1'(A_105, B_106, C_107), A_105) | ~r1_tarski(C_107, B_106) | ~m1_subset_1(C_107, k1_zfmisc_1(u1_struct_0(A_105))) | ~v2_tex_2(B_106, A_105) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.82/2.05  tff(c_313, plain, (![A_121, B_122, A_123]: (v3_pre_topc('#skF_1'(A_121, B_122, A_123), A_121) | ~r1_tarski(A_123, B_122) | ~v2_tex_2(B_122, A_121) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121) | ~r1_tarski(A_123, u1_struct_0(A_121)))), inference(resolution, [status(thm)], [c_14, c_208])).
% 3.82/2.05  tff(c_325, plain, (![A_121, A_7, A_123]: (v3_pre_topc('#skF_1'(A_121, A_7, A_123), A_121) | ~r1_tarski(A_123, A_7) | ~v2_tex_2(A_7, A_121) | ~l1_pre_topc(A_121) | ~r1_tarski(A_123, u1_struct_0(A_121)) | ~r1_tarski(A_7, u1_struct_0(A_121)))), inference(resolution, [status(thm)], [c_14, c_313])).
% 3.82/2.05  tff(c_349, plain, (![A_138, B_139, C_140]: (k9_subset_1(u1_struct_0(A_138), B_139, '#skF_1'(A_138, B_139, C_140))=C_140 | ~r1_tarski(C_140, B_139) | ~m1_subset_1(C_140, k1_zfmisc_1(u1_struct_0(A_138))) | ~v2_tex_2(B_139, A_138) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_138))) | ~l1_pre_topc(A_138))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.82/2.05  tff(c_400, plain, (![A_143, B_144, A_145]: (k9_subset_1(u1_struct_0(A_143), B_144, '#skF_1'(A_143, B_144, A_145))=A_145 | ~r1_tarski(A_145, B_144) | ~v2_tex_2(B_144, A_143) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143) | ~r1_tarski(A_145, u1_struct_0(A_143)))), inference(resolution, [status(thm)], [c_14, c_349])).
% 3.82/2.05  tff(c_412, plain, (![A_143, A_7, A_145]: (k9_subset_1(u1_struct_0(A_143), A_7, '#skF_1'(A_143, A_7, A_145))=A_145 | ~r1_tarski(A_145, A_7) | ~v2_tex_2(A_7, A_143) | ~l1_pre_topc(A_143) | ~r1_tarski(A_145, u1_struct_0(A_143)) | ~r1_tarski(A_7, u1_struct_0(A_143)))), inference(resolution, [status(thm)], [c_14, c_400])).
% 3.82/2.05  tff(c_275, plain, (![A_118, B_119, C_120]: (m1_subset_1('#skF_1'(A_118, B_119, C_120), k1_zfmisc_1(u1_struct_0(A_118))) | ~r1_tarski(C_120, B_119) | ~m1_subset_1(C_120, k1_zfmisc_1(u1_struct_0(A_118))) | ~v2_tex_2(B_119, A_118) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.82/2.05  tff(c_30, plain, (![D_48]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', D_48)!=k1_tarski('#skF_5') | ~v3_pre_topc(D_48, '#skF_3') | ~m1_subset_1(D_48, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.82/2.05  tff(c_295, plain, (![B_119, C_120]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_119, C_120))!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', B_119, C_120), '#skF_3') | ~r1_tarski(C_120, B_119) | ~m1_subset_1(C_120, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_119, '#skF_3') | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_275, c_30])).
% 3.82/2.05  tff(c_518, plain, (![B_159, C_160]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_159, C_160))!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', B_159, C_160), '#skF_3') | ~r1_tarski(C_160, B_159) | ~m1_subset_1(C_160, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_159, '#skF_3') | ~m1_subset_1(B_159, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_295])).
% 3.82/2.05  tff(c_521, plain, (![A_145]: (k1_tarski('#skF_5')!=A_145 | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', A_145), '#skF_3') | ~r1_tarski(A_145, '#skF_4') | ~m1_subset_1(A_145, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_145, '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_145, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_4', u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_412, c_518])).
% 3.82/2.05  tff(c_534, plain, (![A_161]: (k1_tarski('#skF_5')!=A_161 | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', A_161), '#skF_3') | ~m1_subset_1(A_161, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_161, '#skF_4') | ~r1_tarski(A_161, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_40, c_36, c_38, c_36, c_521])).
% 3.82/2.05  tff(c_561, plain, (![A_162]: (k1_tarski('#skF_5')!=A_162 | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', A_162), '#skF_3') | ~r1_tarski(A_162, '#skF_4') | ~r1_tarski(A_162, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_14, c_534])).
% 3.82/2.05  tff(c_569, plain, (![A_123]: (k1_tarski('#skF_5')!=A_123 | ~r1_tarski(A_123, '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_123, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_4', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_325, c_561])).
% 3.82/2.05  tff(c_588, plain, (![A_163]: (k1_tarski('#skF_5')!=A_163 | ~r1_tarski(A_163, '#skF_4') | ~r1_tarski(A_163, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_40, c_36, c_569])).
% 3.82/2.05  tff(c_622, plain, (![A_164]: (k1_tarski(A_164)!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_164), '#skF_4') | ~r2_hidden(A_164, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_96, c_588])).
% 3.82/2.05  tff(c_626, plain, (![A_5]: (k1_tarski(A_5)!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_5), '#skF_4') | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1(A_5, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_10, c_622])).
% 3.82/2.05  tff(c_630, plain, (![A_165]: (k1_tarski(A_165)!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_165), '#skF_4') | ~m1_subset_1(A_165, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_99, c_626])).
% 3.82/2.05  tff(c_636, plain, (![A_166]: (k1_tarski(A_166)!=k1_tarski('#skF_5') | ~m1_subset_1(A_166, u1_struct_0('#skF_3')) | ~r2_hidden(A_166, '#skF_4'))), inference(resolution, [status(thm)], [c_96, c_630])).
% 3.82/2.05  tff(c_639, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_636])).
% 3.82/2.05  tff(c_643, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_639])).
% 3.82/2.05  tff(c_644, plain, (![A_67]: (~r2_hidden(A_67, '#skF_4'))), inference(splitRight, [status(thm)], [c_86])).
% 3.82/2.05  tff(c_647, plain, $false, inference(negUnitSimplification, [status(thm)], [c_644, c_32])).
% 3.82/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/2.05  
% 3.82/2.05  Inference rules
% 3.82/2.05  ----------------------
% 3.82/2.05  #Ref     : 0
% 3.82/2.05  #Sup     : 118
% 3.82/2.05  #Fact    : 0
% 3.82/2.05  #Define  : 0
% 3.82/2.05  #Split   : 3
% 3.82/2.05  #Chain   : 0
% 3.82/2.06  #Close   : 0
% 3.82/2.06  
% 3.82/2.06  Ordering : KBO
% 3.82/2.06  
% 3.82/2.06  Simplification rules
% 3.82/2.06  ----------------------
% 3.82/2.06  #Subsume      : 19
% 3.82/2.06  #Demod        : 76
% 3.82/2.06  #Tautology    : 28
% 3.82/2.06  #SimpNegUnit  : 2
% 3.82/2.06  #BackRed      : 1
% 3.82/2.06  
% 3.82/2.06  #Partial instantiations: 0
% 3.82/2.06  #Strategies tried      : 1
% 3.82/2.06  
% 3.82/2.06  Timing (in seconds)
% 3.82/2.06  ----------------------
% 3.82/2.06  Preprocessing        : 0.48
% 3.82/2.06  Parsing              : 0.24
% 3.82/2.06  CNF conversion       : 0.04
% 3.82/2.06  Main loop            : 0.61
% 3.82/2.06  Inferencing          : 0.24
% 3.82/2.06  Reduction            : 0.17
% 3.82/2.06  Demodulation         : 0.12
% 3.82/2.06  BG Simplification    : 0.03
% 3.82/2.06  Subsumption          : 0.12
% 3.82/2.06  Abstraction          : 0.03
% 3.82/2.06  MUC search           : 0.00
% 3.82/2.06  Cooper               : 0.00
% 3.82/2.06  Total                : 1.15
% 3.82/2.06  Index Insertion      : 0.00
% 3.82/2.06  Index Deletion       : 0.00
% 3.82/2.06  Index Matching       : 0.00
% 3.82/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------

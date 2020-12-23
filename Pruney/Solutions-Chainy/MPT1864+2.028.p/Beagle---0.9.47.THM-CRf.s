%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:17 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 106 expanded)
%              Number of leaves         :   26 (  50 expanded)
%              Depth                    :   15
%              Number of atoms          :  154 ( 325 expanded)
%              Number of equality atoms :   18 (  34 expanded)
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

tff(f_91,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_69,axiom,(
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

tff(c_28,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_67,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(k1_tarski(A_56),k1_zfmisc_1(B_57))
      | ~ r2_hidden(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_76,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(k1_tarski(A_56),B_57)
      | ~ r2_hidden(A_56,B_57) ) ),
    inference(resolution,[status(thm)],[c_67,c_8])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_78,plain,(
    ! [C_60,B_61,A_62] :
      ( ~ v1_xboole_0(C_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(C_60))
      | ~ r2_hidden(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_87,plain,(
    ! [A_62] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_62,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_78])).

tff(c_88,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_46,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_50,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_46])).

tff(c_36,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_32,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_194,plain,(
    ! [A_91,B_92,C_93] :
      ( v3_pre_topc('#skF_1'(A_91,B_92,C_93),A_91)
      | ~ r1_tarski(C_93,B_92)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ v2_tex_2(B_92,A_91)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_320,plain,(
    ! [A_112,B_113,A_114] :
      ( v3_pre_topc('#skF_1'(A_112,B_113,A_114),A_112)
      | ~ r1_tarski(A_114,B_113)
      | ~ v2_tex_2(B_113,A_112)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112)
      | ~ r1_tarski(A_114,u1_struct_0(A_112)) ) ),
    inference(resolution,[status(thm)],[c_10,c_194])).

tff(c_336,plain,(
    ! [A_112,A_6,A_114] :
      ( v3_pre_topc('#skF_1'(A_112,A_6,A_114),A_112)
      | ~ r1_tarski(A_114,A_6)
      | ~ v2_tex_2(A_6,A_112)
      | ~ l1_pre_topc(A_112)
      | ~ r1_tarski(A_114,u1_struct_0(A_112))
      | ~ r1_tarski(A_6,u1_struct_0(A_112)) ) ),
    inference(resolution,[status(thm)],[c_10,c_320])).

tff(c_365,plain,(
    ! [A_143,B_144,C_145] :
      ( k9_subset_1(u1_struct_0(A_143),B_144,'#skF_1'(A_143,B_144,C_145)) = C_145
      | ~ r1_tarski(C_145,B_144)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ v2_tex_2(B_144,A_143)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_411,plain,(
    ! [A_147,B_148,A_149] :
      ( k9_subset_1(u1_struct_0(A_147),B_148,'#skF_1'(A_147,B_148,A_149)) = A_149
      | ~ r1_tarski(A_149,B_148)
      | ~ v2_tex_2(B_148,A_147)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ l1_pre_topc(A_147)
      | ~ r1_tarski(A_149,u1_struct_0(A_147)) ) ),
    inference(resolution,[status(thm)],[c_10,c_365])).

tff(c_423,plain,(
    ! [A_149] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3','#skF_4',A_149)) = A_149
      | ~ r1_tarski(A_149,'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_149,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_34,c_411])).

tff(c_431,plain,(
    ! [A_150] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3','#skF_4',A_150)) = A_150
      | ~ r1_tarski(A_150,'#skF_4')
      | ~ r1_tarski(A_150,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_423])).

tff(c_280,plain,(
    ! [A_105,B_106,C_107] :
      ( m1_subset_1('#skF_1'(A_105,B_106,C_107),k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ r1_tarski(C_107,B_106)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ v2_tex_2(B_106,A_105)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_26,plain,(
    ! [D_47] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',D_47) != k1_tarski('#skF_5')
      | ~ v3_pre_topc(D_47,'#skF_3')
      | ~ m1_subset_1(D_47,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_300,plain,(
    ! [B_106,C_107] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_106,C_107)) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_106,C_107),'#skF_3')
      | ~ r1_tarski(C_107,B_106)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_106,'#skF_3')
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_280,c_26])).

tff(c_316,plain,(
    ! [B_106,C_107] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_106,C_107)) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_106,C_107),'#skF_3')
      | ~ r1_tarski(C_107,B_106)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_106,'#skF_3')
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_300])).

tff(c_436,plain,(
    ! [A_150] :
      ( k1_tarski('#skF_5') != A_150
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',A_150),'#skF_3')
      | ~ r1_tarski(A_150,'#skF_4')
      | ~ m1_subset_1(A_150,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_150,'#skF_4')
      | ~ r1_tarski(A_150,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_316])).

tff(c_479,plain,(
    ! [A_152] :
      ( k1_tarski('#skF_5') != A_152
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',A_152),'#skF_3')
      | ~ m1_subset_1(A_152,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_152,'#skF_4')
      | ~ r1_tarski(A_152,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_436])).

tff(c_532,plain,(
    ! [A_154] :
      ( k1_tarski('#skF_5') != A_154
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',A_154),'#skF_3')
      | ~ r1_tarski(A_154,'#skF_4')
      | ~ r1_tarski(A_154,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_10,c_479])).

tff(c_540,plain,(
    ! [A_114] :
      ( k1_tarski('#skF_5') != A_114
      | ~ r1_tarski(A_114,'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_114,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_4',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_336,c_532])).

tff(c_559,plain,(
    ! [A_155] :
      ( k1_tarski('#skF_5') != A_155
      | ~ r1_tarski(A_155,'#skF_4')
      | ~ r1_tarski(A_155,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_36,c_32,c_540])).

tff(c_588,plain,(
    ! [A_156] :
      ( k1_tarski(A_156) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_156),'#skF_4')
      | ~ r2_hidden(A_156,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_76,c_559])).

tff(c_592,plain,(
    ! [A_4] :
      ( k1_tarski(A_4) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_4),'#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_4,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_6,c_588])).

tff(c_596,plain,(
    ! [A_157] :
      ( k1_tarski(A_157) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_157),'#skF_4')
      | ~ m1_subset_1(A_157,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_592])).

tff(c_607,plain,(
    ! [A_162] :
      ( k1_tarski(A_162) != k1_tarski('#skF_5')
      | ~ m1_subset_1(A_162,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_162,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_76,c_596])).

tff(c_610,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_607])).

tff(c_614,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_610])).

tff(c_615,plain,(
    ! [A_62] : ~ r2_hidden(A_62,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_618,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_615,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:34:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.43  
% 2.71/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.43  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.71/1.43  
% 2.71/1.43  %Foreground sorts:
% 2.71/1.43  
% 2.71/1.43  
% 2.71/1.43  %Background operators:
% 2.71/1.43  
% 2.71/1.43  
% 2.71/1.43  %Foreground operators:
% 2.71/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.71/1.43  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.71/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.71/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.71/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.71/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.71/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.71/1.43  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.71/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.71/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.71/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.71/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.71/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.71/1.43  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.71/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.71/1.43  
% 2.71/1.45  tff(f_91, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_tex_2)).
% 2.71/1.45  tff(f_31, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 2.71/1.45  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.71/1.45  tff(f_48, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.71/1.45  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.71/1.45  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 2.71/1.45  tff(c_28, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.71/1.45  tff(c_30, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.71/1.45  tff(c_67, plain, (![A_56, B_57]: (m1_subset_1(k1_tarski(A_56), k1_zfmisc_1(B_57)) | ~r2_hidden(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.71/1.45  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.71/1.45  tff(c_76, plain, (![A_56, B_57]: (r1_tarski(k1_tarski(A_56), B_57) | ~r2_hidden(A_56, B_57))), inference(resolution, [status(thm)], [c_67, c_8])).
% 2.71/1.45  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.71/1.45  tff(c_78, plain, (![C_60, B_61, A_62]: (~v1_xboole_0(C_60) | ~m1_subset_1(B_61, k1_zfmisc_1(C_60)) | ~r2_hidden(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.71/1.45  tff(c_87, plain, (![A_62]: (~v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden(A_62, '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_78])).
% 2.71/1.45  tff(c_88, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_87])).
% 2.71/1.45  tff(c_6, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.71/1.45  tff(c_46, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.71/1.45  tff(c_50, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_46])).
% 2.71/1.45  tff(c_36, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.71/1.45  tff(c_32, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.71/1.45  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.71/1.45  tff(c_194, plain, (![A_91, B_92, C_93]: (v3_pre_topc('#skF_1'(A_91, B_92, C_93), A_91) | ~r1_tarski(C_93, B_92) | ~m1_subset_1(C_93, k1_zfmisc_1(u1_struct_0(A_91))) | ~v2_tex_2(B_92, A_91) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.71/1.45  tff(c_320, plain, (![A_112, B_113, A_114]: (v3_pre_topc('#skF_1'(A_112, B_113, A_114), A_112) | ~r1_tarski(A_114, B_113) | ~v2_tex_2(B_113, A_112) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112) | ~r1_tarski(A_114, u1_struct_0(A_112)))), inference(resolution, [status(thm)], [c_10, c_194])).
% 2.71/1.45  tff(c_336, plain, (![A_112, A_6, A_114]: (v3_pre_topc('#skF_1'(A_112, A_6, A_114), A_112) | ~r1_tarski(A_114, A_6) | ~v2_tex_2(A_6, A_112) | ~l1_pre_topc(A_112) | ~r1_tarski(A_114, u1_struct_0(A_112)) | ~r1_tarski(A_6, u1_struct_0(A_112)))), inference(resolution, [status(thm)], [c_10, c_320])).
% 2.71/1.45  tff(c_365, plain, (![A_143, B_144, C_145]: (k9_subset_1(u1_struct_0(A_143), B_144, '#skF_1'(A_143, B_144, C_145))=C_145 | ~r1_tarski(C_145, B_144) | ~m1_subset_1(C_145, k1_zfmisc_1(u1_struct_0(A_143))) | ~v2_tex_2(B_144, A_143) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.71/1.45  tff(c_411, plain, (![A_147, B_148, A_149]: (k9_subset_1(u1_struct_0(A_147), B_148, '#skF_1'(A_147, B_148, A_149))=A_149 | ~r1_tarski(A_149, B_148) | ~v2_tex_2(B_148, A_147) | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0(A_147))) | ~l1_pre_topc(A_147) | ~r1_tarski(A_149, u1_struct_0(A_147)))), inference(resolution, [status(thm)], [c_10, c_365])).
% 2.71/1.45  tff(c_423, plain, (![A_149]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', '#skF_4', A_149))=A_149 | ~r1_tarski(A_149, '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_149, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_34, c_411])).
% 2.71/1.45  tff(c_431, plain, (![A_150]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', '#skF_4', A_150))=A_150 | ~r1_tarski(A_150, '#skF_4') | ~r1_tarski(A_150, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_423])).
% 2.71/1.45  tff(c_280, plain, (![A_105, B_106, C_107]: (m1_subset_1('#skF_1'(A_105, B_106, C_107), k1_zfmisc_1(u1_struct_0(A_105))) | ~r1_tarski(C_107, B_106) | ~m1_subset_1(C_107, k1_zfmisc_1(u1_struct_0(A_105))) | ~v2_tex_2(B_106, A_105) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.71/1.45  tff(c_26, plain, (![D_47]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', D_47)!=k1_tarski('#skF_5') | ~v3_pre_topc(D_47, '#skF_3') | ~m1_subset_1(D_47, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.71/1.45  tff(c_300, plain, (![B_106, C_107]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_106, C_107))!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', B_106, C_107), '#skF_3') | ~r1_tarski(C_107, B_106) | ~m1_subset_1(C_107, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_106, '#skF_3') | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_280, c_26])).
% 2.71/1.45  tff(c_316, plain, (![B_106, C_107]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_106, C_107))!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', B_106, C_107), '#skF_3') | ~r1_tarski(C_107, B_106) | ~m1_subset_1(C_107, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_106, '#skF_3') | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_300])).
% 2.71/1.45  tff(c_436, plain, (![A_150]: (k1_tarski('#skF_5')!=A_150 | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', A_150), '#skF_3') | ~r1_tarski(A_150, '#skF_4') | ~m1_subset_1(A_150, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_150, '#skF_4') | ~r1_tarski(A_150, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_431, c_316])).
% 2.71/1.45  tff(c_479, plain, (![A_152]: (k1_tarski('#skF_5')!=A_152 | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', A_152), '#skF_3') | ~m1_subset_1(A_152, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_152, '#skF_4') | ~r1_tarski(A_152, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_436])).
% 2.71/1.45  tff(c_532, plain, (![A_154]: (k1_tarski('#skF_5')!=A_154 | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', A_154), '#skF_3') | ~r1_tarski(A_154, '#skF_4') | ~r1_tarski(A_154, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_10, c_479])).
% 2.71/1.45  tff(c_540, plain, (![A_114]: (k1_tarski('#skF_5')!=A_114 | ~r1_tarski(A_114, '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_114, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_4', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_336, c_532])).
% 2.71/1.45  tff(c_559, plain, (![A_155]: (k1_tarski('#skF_5')!=A_155 | ~r1_tarski(A_155, '#skF_4') | ~r1_tarski(A_155, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_36, c_32, c_540])).
% 2.71/1.45  tff(c_588, plain, (![A_156]: (k1_tarski(A_156)!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_156), '#skF_4') | ~r2_hidden(A_156, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_76, c_559])).
% 2.71/1.45  tff(c_592, plain, (![A_4]: (k1_tarski(A_4)!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_4), '#skF_4') | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1(A_4, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_6, c_588])).
% 2.71/1.45  tff(c_596, plain, (![A_157]: (k1_tarski(A_157)!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_157), '#skF_4') | ~m1_subset_1(A_157, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_88, c_592])).
% 2.71/1.45  tff(c_607, plain, (![A_162]: (k1_tarski(A_162)!=k1_tarski('#skF_5') | ~m1_subset_1(A_162, u1_struct_0('#skF_3')) | ~r2_hidden(A_162, '#skF_4'))), inference(resolution, [status(thm)], [c_76, c_596])).
% 2.71/1.45  tff(c_610, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_607])).
% 2.71/1.45  tff(c_614, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_610])).
% 2.71/1.45  tff(c_615, plain, (![A_62]: (~r2_hidden(A_62, '#skF_4'))), inference(splitRight, [status(thm)], [c_87])).
% 2.71/1.45  tff(c_618, plain, $false, inference(negUnitSimplification, [status(thm)], [c_615, c_28])).
% 2.71/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.45  
% 2.71/1.45  Inference rules
% 2.71/1.45  ----------------------
% 2.71/1.45  #Ref     : 0
% 2.71/1.45  #Sup     : 114
% 2.71/1.45  #Fact    : 0
% 2.71/1.45  #Define  : 0
% 2.71/1.45  #Split   : 4
% 2.71/1.45  #Chain   : 0
% 2.71/1.45  #Close   : 0
% 2.71/1.45  
% 2.71/1.45  Ordering : KBO
% 2.71/1.45  
% 2.71/1.45  Simplification rules
% 2.71/1.45  ----------------------
% 2.71/1.45  #Subsume      : 18
% 2.71/1.45  #Demod        : 55
% 2.71/1.45  #Tautology    : 17
% 2.71/1.45  #SimpNegUnit  : 2
% 2.71/1.45  #BackRed      : 1
% 2.71/1.45  
% 2.71/1.45  #Partial instantiations: 0
% 2.71/1.45  #Strategies tried      : 1
% 2.71/1.45  
% 2.71/1.45  Timing (in seconds)
% 2.71/1.45  ----------------------
% 2.71/1.45  Preprocessing        : 0.31
% 2.71/1.45  Parsing              : 0.17
% 2.71/1.45  CNF conversion       : 0.02
% 3.08/1.45  Main loop            : 0.35
% 3.08/1.45  Inferencing          : 0.14
% 3.08/1.45  Reduction            : 0.09
% 3.08/1.45  Demodulation         : 0.06
% 3.08/1.45  BG Simplification    : 0.02
% 3.08/1.45  Subsumption          : 0.07
% 3.08/1.45  Abstraction          : 0.02
% 3.08/1.45  MUC search           : 0.00
% 3.08/1.45  Cooper               : 0.00
% 3.08/1.45  Total                : 0.69
% 3.08/1.45  Index Insertion      : 0.00
% 3.08/1.45  Index Deletion       : 0.00
% 3.08/1.45  Index Matching       : 0.00
% 3.08/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------

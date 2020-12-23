%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:22 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 107 expanded)
%              Number of leaves         :   27 (  51 expanded)
%              Depth                    :   15
%              Number of atoms          :  154 ( 325 expanded)
%              Number of equality atoms :   18 (  34 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k1_enumset1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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
                         => ~ ( v4_pre_topc(D,A)
                              & k9_subset_1(u1_struct_0(A),B,D) = k1_tarski(C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tex_2)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).

tff(c_30,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_78,plain,(
    ! [A_60,B_61] :
      ( m1_subset_1(k1_tarski(A_60),k1_zfmisc_1(B_61))
      | ~ r2_hidden(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_87,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(k1_tarski(A_60),B_61)
      | ~ r2_hidden(A_60,B_61) ) ),
    inference(resolution,[status(thm)],[c_78,c_10])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_89,plain,(
    ! [C_64,B_65,A_66] :
      ( ~ v1_xboole_0(C_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(C_64))
      | ~ r2_hidden(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_98,plain,(
    ! [A_66] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_66,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_89])).

tff(c_113,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_48,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(A_51,B_52)
      | ~ m1_subset_1(A_51,k1_zfmisc_1(B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_52,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_48])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_34,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_200,plain,(
    ! [A_92,B_93,C_94] :
      ( v4_pre_topc('#skF_1'(A_92,B_93,C_94),A_92)
      | ~ r1_tarski(C_94,B_93)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ v2_tex_2(B_93,A_92)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_294,plain,(
    ! [A_116,B_117,A_118] :
      ( v4_pre_topc('#skF_1'(A_116,B_117,A_118),A_116)
      | ~ r1_tarski(A_118,B_117)
      | ~ v2_tex_2(B_117,A_116)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116)
      | ~ r1_tarski(A_118,u1_struct_0(A_116)) ) ),
    inference(resolution,[status(thm)],[c_12,c_200])).

tff(c_307,plain,(
    ! [A_116,A_8,A_118] :
      ( v4_pre_topc('#skF_1'(A_116,A_8,A_118),A_116)
      | ~ r1_tarski(A_118,A_8)
      | ~ v2_tex_2(A_8,A_116)
      | ~ l1_pre_topc(A_116)
      | ~ r1_tarski(A_118,u1_struct_0(A_116))
      | ~ r1_tarski(A_8,u1_struct_0(A_116)) ) ),
    inference(resolution,[status(thm)],[c_12,c_294])).

tff(c_376,plain,(
    ! [A_147,B_148,C_149] :
      ( k9_subset_1(u1_struct_0(A_147),B_148,'#skF_1'(A_147,B_148,C_149)) = C_149
      | ~ r1_tarski(C_149,B_148)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ v2_tex_2(B_148,A_147)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ l1_pre_topc(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_461,plain,(
    ! [A_153,B_154,A_155] :
      ( k9_subset_1(u1_struct_0(A_153),B_154,'#skF_1'(A_153,B_154,A_155)) = A_155
      | ~ r1_tarski(A_155,B_154)
      | ~ v2_tex_2(B_154,A_153)
      | ~ m1_subset_1(B_154,k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ l1_pre_topc(A_153)
      | ~ r1_tarski(A_155,u1_struct_0(A_153)) ) ),
    inference(resolution,[status(thm)],[c_12,c_376])).

tff(c_473,plain,(
    ! [A_155] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3','#skF_4',A_155)) = A_155
      | ~ r1_tarski(A_155,'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_155,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_36,c_461])).

tff(c_481,plain,(
    ! [A_156] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3','#skF_4',A_156)) = A_156
      | ~ r1_tarski(A_156,'#skF_4')
      | ~ r1_tarski(A_156,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_473])).

tff(c_317,plain,(
    ! [A_125,B_126,C_127] :
      ( m1_subset_1('#skF_1'(A_125,B_126,C_127),k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ r1_tarski(C_127,B_126)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ v2_tex_2(B_126,A_125)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_28,plain,(
    ! [D_49] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',D_49) != k1_tarski('#skF_5')
      | ~ v4_pre_topc(D_49,'#skF_3')
      | ~ m1_subset_1(D_49,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_339,plain,(
    ! [B_126,C_127] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_126,C_127)) != k1_tarski('#skF_5')
      | ~ v4_pre_topc('#skF_1'('#skF_3',B_126,C_127),'#skF_3')
      | ~ r1_tarski(C_127,B_126)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_126,'#skF_3')
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_317,c_28])).

tff(c_356,plain,(
    ! [B_126,C_127] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_126,C_127)) != k1_tarski('#skF_5')
      | ~ v4_pre_topc('#skF_1'('#skF_3',B_126,C_127),'#skF_3')
      | ~ r1_tarski(C_127,B_126)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_126,'#skF_3')
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_339])).

tff(c_490,plain,(
    ! [A_156] :
      ( k1_tarski('#skF_5') != A_156
      | ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4',A_156),'#skF_3')
      | ~ r1_tarski(A_156,'#skF_4')
      | ~ m1_subset_1(A_156,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_156,'#skF_4')
      | ~ r1_tarski(A_156,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_481,c_356])).

tff(c_511,plain,(
    ! [A_157] :
      ( k1_tarski('#skF_5') != A_157
      | ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4',A_157),'#skF_3')
      | ~ m1_subset_1(A_157,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_157,'#skF_4')
      | ~ r1_tarski(A_157,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_490])).

tff(c_543,plain,(
    ! [A_158] :
      ( k1_tarski('#skF_5') != A_158
      | ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4',A_158),'#skF_3')
      | ~ r1_tarski(A_158,'#skF_4')
      | ~ r1_tarski(A_158,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_12,c_511])).

tff(c_551,plain,(
    ! [A_118] :
      ( k1_tarski('#skF_5') != A_118
      | ~ r1_tarski(A_118,'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_118,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_4',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_307,c_543])).

tff(c_570,plain,(
    ! [A_159] :
      ( k1_tarski('#skF_5') != A_159
      | ~ r1_tarski(A_159,'#skF_4')
      | ~ r1_tarski(A_159,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_38,c_34,c_551])).

tff(c_599,plain,(
    ! [A_160] :
      ( k1_tarski(A_160) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_160),'#skF_4')
      | ~ r2_hidden(A_160,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_87,c_570])).

tff(c_603,plain,(
    ! [A_6] :
      ( k1_tarski(A_6) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_6),'#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_6,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_8,c_599])).

tff(c_612,plain,(
    ! [A_165] :
      ( k1_tarski(A_165) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_165),'#skF_4')
      | ~ m1_subset_1(A_165,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_603])).

tff(c_618,plain,(
    ! [A_166] :
      ( k1_tarski(A_166) != k1_tarski('#skF_5')
      | ~ m1_subset_1(A_166,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_166,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_87,c_612])).

tff(c_621,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_618])).

tff(c_625,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_621])).

tff(c_626,plain,(
    ! [A_66] : ~ r2_hidden(A_66,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_629,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_626,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:54:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.42  
% 3.06/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.43  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k1_enumset1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.06/1.43  
% 3.06/1.43  %Foreground sorts:
% 3.06/1.43  
% 3.06/1.43  
% 3.06/1.43  %Background operators:
% 3.06/1.43  
% 3.06/1.43  
% 3.06/1.43  %Foreground operators:
% 3.06/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.06/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.06/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.06/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.06/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.06/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.06/1.43  tff('#skF_5', type, '#skF_5': $i).
% 3.06/1.43  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.06/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.06/1.43  tff('#skF_3', type, '#skF_3': $i).
% 3.06/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.06/1.43  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.06/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.43  tff('#skF_4', type, '#skF_4': $i).
% 3.06/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.06/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.06/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.06/1.43  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.06/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.06/1.43  
% 3.13/1.44  tff(f_93, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tex_2)).
% 3.13/1.44  tff(f_33, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 3.13/1.44  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.13/1.44  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.13/1.44  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.13/1.44  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tex_2)).
% 3.13/1.44  tff(c_30, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.13/1.44  tff(c_32, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.13/1.44  tff(c_78, plain, (![A_60, B_61]: (m1_subset_1(k1_tarski(A_60), k1_zfmisc_1(B_61)) | ~r2_hidden(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.13/1.44  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.13/1.44  tff(c_87, plain, (![A_60, B_61]: (r1_tarski(k1_tarski(A_60), B_61) | ~r2_hidden(A_60, B_61))), inference(resolution, [status(thm)], [c_78, c_10])).
% 3.13/1.44  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.13/1.44  tff(c_89, plain, (![C_64, B_65, A_66]: (~v1_xboole_0(C_64) | ~m1_subset_1(B_65, k1_zfmisc_1(C_64)) | ~r2_hidden(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.13/1.44  tff(c_98, plain, (![A_66]: (~v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden(A_66, '#skF_4'))), inference(resolution, [status(thm)], [c_36, c_89])).
% 3.13/1.44  tff(c_113, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_98])).
% 3.13/1.44  tff(c_8, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | v1_xboole_0(B_7) | ~m1_subset_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.13/1.44  tff(c_48, plain, (![A_51, B_52]: (r1_tarski(A_51, B_52) | ~m1_subset_1(A_51, k1_zfmisc_1(B_52)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.13/1.44  tff(c_52, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_48])).
% 3.13/1.44  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.13/1.44  tff(c_34, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.13/1.44  tff(c_12, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.13/1.44  tff(c_200, plain, (![A_92, B_93, C_94]: (v4_pre_topc('#skF_1'(A_92, B_93, C_94), A_92) | ~r1_tarski(C_94, B_93) | ~m1_subset_1(C_94, k1_zfmisc_1(u1_struct_0(A_92))) | ~v2_tex_2(B_93, A_92) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.13/1.44  tff(c_294, plain, (![A_116, B_117, A_118]: (v4_pre_topc('#skF_1'(A_116, B_117, A_118), A_116) | ~r1_tarski(A_118, B_117) | ~v2_tex_2(B_117, A_116) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116) | ~r1_tarski(A_118, u1_struct_0(A_116)))), inference(resolution, [status(thm)], [c_12, c_200])).
% 3.13/1.44  tff(c_307, plain, (![A_116, A_8, A_118]: (v4_pre_topc('#skF_1'(A_116, A_8, A_118), A_116) | ~r1_tarski(A_118, A_8) | ~v2_tex_2(A_8, A_116) | ~l1_pre_topc(A_116) | ~r1_tarski(A_118, u1_struct_0(A_116)) | ~r1_tarski(A_8, u1_struct_0(A_116)))), inference(resolution, [status(thm)], [c_12, c_294])).
% 3.13/1.44  tff(c_376, plain, (![A_147, B_148, C_149]: (k9_subset_1(u1_struct_0(A_147), B_148, '#skF_1'(A_147, B_148, C_149))=C_149 | ~r1_tarski(C_149, B_148) | ~m1_subset_1(C_149, k1_zfmisc_1(u1_struct_0(A_147))) | ~v2_tex_2(B_148, A_147) | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0(A_147))) | ~l1_pre_topc(A_147))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.13/1.44  tff(c_461, plain, (![A_153, B_154, A_155]: (k9_subset_1(u1_struct_0(A_153), B_154, '#skF_1'(A_153, B_154, A_155))=A_155 | ~r1_tarski(A_155, B_154) | ~v2_tex_2(B_154, A_153) | ~m1_subset_1(B_154, k1_zfmisc_1(u1_struct_0(A_153))) | ~l1_pre_topc(A_153) | ~r1_tarski(A_155, u1_struct_0(A_153)))), inference(resolution, [status(thm)], [c_12, c_376])).
% 3.13/1.44  tff(c_473, plain, (![A_155]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', '#skF_4', A_155))=A_155 | ~r1_tarski(A_155, '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_155, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_36, c_461])).
% 3.13/1.44  tff(c_481, plain, (![A_156]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', '#skF_4', A_156))=A_156 | ~r1_tarski(A_156, '#skF_4') | ~r1_tarski(A_156, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_473])).
% 3.13/1.44  tff(c_317, plain, (![A_125, B_126, C_127]: (m1_subset_1('#skF_1'(A_125, B_126, C_127), k1_zfmisc_1(u1_struct_0(A_125))) | ~r1_tarski(C_127, B_126) | ~m1_subset_1(C_127, k1_zfmisc_1(u1_struct_0(A_125))) | ~v2_tex_2(B_126, A_125) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.13/1.44  tff(c_28, plain, (![D_49]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', D_49)!=k1_tarski('#skF_5') | ~v4_pre_topc(D_49, '#skF_3') | ~m1_subset_1(D_49, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.13/1.44  tff(c_339, plain, (![B_126, C_127]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_126, C_127))!=k1_tarski('#skF_5') | ~v4_pre_topc('#skF_1'('#skF_3', B_126, C_127), '#skF_3') | ~r1_tarski(C_127, B_126) | ~m1_subset_1(C_127, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_126, '#skF_3') | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_317, c_28])).
% 3.13/1.44  tff(c_356, plain, (![B_126, C_127]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_126, C_127))!=k1_tarski('#skF_5') | ~v4_pre_topc('#skF_1'('#skF_3', B_126, C_127), '#skF_3') | ~r1_tarski(C_127, B_126) | ~m1_subset_1(C_127, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_126, '#skF_3') | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_339])).
% 3.13/1.44  tff(c_490, plain, (![A_156]: (k1_tarski('#skF_5')!=A_156 | ~v4_pre_topc('#skF_1'('#skF_3', '#skF_4', A_156), '#skF_3') | ~r1_tarski(A_156, '#skF_4') | ~m1_subset_1(A_156, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_156, '#skF_4') | ~r1_tarski(A_156, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_481, c_356])).
% 3.13/1.44  tff(c_511, plain, (![A_157]: (k1_tarski('#skF_5')!=A_157 | ~v4_pre_topc('#skF_1'('#skF_3', '#skF_4', A_157), '#skF_3') | ~m1_subset_1(A_157, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_157, '#skF_4') | ~r1_tarski(A_157, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_490])).
% 3.13/1.44  tff(c_543, plain, (![A_158]: (k1_tarski('#skF_5')!=A_158 | ~v4_pre_topc('#skF_1'('#skF_3', '#skF_4', A_158), '#skF_3') | ~r1_tarski(A_158, '#skF_4') | ~r1_tarski(A_158, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_12, c_511])).
% 3.13/1.44  tff(c_551, plain, (![A_118]: (k1_tarski('#skF_5')!=A_118 | ~r1_tarski(A_118, '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_118, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_4', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_307, c_543])).
% 3.13/1.44  tff(c_570, plain, (![A_159]: (k1_tarski('#skF_5')!=A_159 | ~r1_tarski(A_159, '#skF_4') | ~r1_tarski(A_159, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_38, c_34, c_551])).
% 3.13/1.44  tff(c_599, plain, (![A_160]: (k1_tarski(A_160)!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_160), '#skF_4') | ~r2_hidden(A_160, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_87, c_570])).
% 3.13/1.44  tff(c_603, plain, (![A_6]: (k1_tarski(A_6)!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_6), '#skF_4') | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1(A_6, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_8, c_599])).
% 3.13/1.44  tff(c_612, plain, (![A_165]: (k1_tarski(A_165)!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_165), '#skF_4') | ~m1_subset_1(A_165, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_113, c_603])).
% 3.13/1.44  tff(c_618, plain, (![A_166]: (k1_tarski(A_166)!=k1_tarski('#skF_5') | ~m1_subset_1(A_166, u1_struct_0('#skF_3')) | ~r2_hidden(A_166, '#skF_4'))), inference(resolution, [status(thm)], [c_87, c_612])).
% 3.13/1.44  tff(c_621, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_618])).
% 3.13/1.44  tff(c_625, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_621])).
% 3.13/1.44  tff(c_626, plain, (![A_66]: (~r2_hidden(A_66, '#skF_4'))), inference(splitRight, [status(thm)], [c_98])).
% 3.13/1.44  tff(c_629, plain, $false, inference(negUnitSimplification, [status(thm)], [c_626, c_30])).
% 3.13/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.44  
% 3.13/1.44  Inference rules
% 3.13/1.44  ----------------------
% 3.13/1.44  #Ref     : 0
% 3.13/1.44  #Sup     : 116
% 3.13/1.44  #Fact    : 0
% 3.13/1.44  #Define  : 0
% 3.13/1.44  #Split   : 4
% 3.13/1.44  #Chain   : 0
% 3.13/1.44  #Close   : 0
% 3.13/1.44  
% 3.13/1.44  Ordering : KBO
% 3.13/1.44  
% 3.13/1.44  Simplification rules
% 3.13/1.44  ----------------------
% 3.13/1.44  #Subsume      : 19
% 3.13/1.44  #Demod        : 55
% 3.13/1.44  #Tautology    : 19
% 3.13/1.44  #SimpNegUnit  : 2
% 3.13/1.44  #BackRed      : 1
% 3.13/1.44  
% 3.13/1.44  #Partial instantiations: 0
% 3.13/1.44  #Strategies tried      : 1
% 3.13/1.44  
% 3.13/1.44  Timing (in seconds)
% 3.13/1.44  ----------------------
% 3.13/1.44  Preprocessing        : 0.31
% 3.13/1.44  Parsing              : 0.16
% 3.13/1.44  CNF conversion       : 0.02
% 3.13/1.44  Main loop            : 0.37
% 3.13/1.44  Inferencing          : 0.14
% 3.13/1.45  Reduction            : 0.10
% 3.13/1.45  Demodulation         : 0.07
% 3.13/1.45  BG Simplification    : 0.02
% 3.13/1.45  Subsumption          : 0.08
% 3.13/1.45  Abstraction          : 0.02
% 3.13/1.45  MUC search           : 0.00
% 3.13/1.45  Cooper               : 0.00
% 3.13/1.45  Total                : 0.71
% 3.13/1.45  Index Insertion      : 0.00
% 3.13/1.45  Index Deletion       : 0.00
% 3.13/1.45  Index Matching       : 0.00
% 3.13/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------

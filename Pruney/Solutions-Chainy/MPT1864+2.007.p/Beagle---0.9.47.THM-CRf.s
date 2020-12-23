%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:14 EST 2020

% Result     : Theorem 10.97s
% Output     : CNFRefutation 10.97s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 150 expanded)
%              Number of leaves         :   26 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :  175 ( 425 expanded)
%              Number of equality atoms :   15 (  39 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tex_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_34,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_65,axiom,(
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

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_52,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(A_50,B_51)
      | ~ m1_subset_1(A_50,k1_zfmisc_1(B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_56,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_52])).

tff(c_8,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_73,plain,(
    ! [A_57,B_58] :
      ( r2_hidden('#skF_1'(A_57,B_58),A_57)
      | r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_78,plain,(
    ! [A_57] : r1_tarski(A_57,A_57) ),
    inference(resolution,[status(thm)],[c_73,c_4])).

tff(c_80,plain,(
    ! [B_60,C_61,A_62] :
      ( r2_hidden(B_60,C_61)
      | ~ r1_tarski(k2_tarski(A_62,B_60),C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_89,plain,(
    ! [B_63,A_64] : r2_hidden(B_63,k2_tarski(A_64,B_63)) ),
    inference(resolution,[status(thm)],[c_78,c_80])).

tff(c_92,plain,(
    ! [A_6] : r2_hidden(A_6,k1_tarski(A_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_89])).

tff(c_34,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_145,plain,(
    ! [A_79,B_80,C_81] :
      ( r1_tarski(k2_tarski(A_79,B_80),C_81)
      | ~ r2_hidden(B_80,C_81)
      | ~ r2_hidden(A_79,C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_156,plain,(
    ! [A_6,C_81] :
      ( r1_tarski(k1_tarski(A_6),C_81)
      | ~ r2_hidden(A_6,C_81)
      | ~ r2_hidden(A_6,C_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_145])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_116,plain,(
    ! [C_73,B_74,A_75] :
      ( r2_hidden(C_73,B_74)
      | ~ r2_hidden(C_73,A_75)
      | ~ r1_tarski(A_75,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_199,plain,(
    ! [A_88,B_89,B_90] :
      ( r2_hidden('#skF_1'(A_88,B_89),B_90)
      | ~ r1_tarski(A_88,B_90)
      | r1_tarski(A_88,B_89) ) ),
    inference(resolution,[status(thm)],[c_6,c_116])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_209,plain,(
    ! [A_91,B_92,B_93,B_94] :
      ( r2_hidden('#skF_1'(A_91,B_92),B_93)
      | ~ r1_tarski(B_94,B_93)
      | ~ r1_tarski(A_91,B_94)
      | r1_tarski(A_91,B_92) ) ),
    inference(resolution,[status(thm)],[c_199,c_2])).

tff(c_377,plain,(
    ! [A_121,B_122,C_123,A_124] :
      ( r2_hidden('#skF_1'(A_121,B_122),C_123)
      | ~ r1_tarski(A_121,k1_tarski(A_124))
      | r1_tarski(A_121,B_122)
      | ~ r2_hidden(A_124,C_123) ) ),
    inference(resolution,[status(thm)],[c_156,c_209])).

tff(c_598,plain,(
    ! [A_161,B_162,C_163,A_164] :
      ( r2_hidden('#skF_1'(k1_tarski(A_161),B_162),C_163)
      | r1_tarski(k1_tarski(A_161),B_162)
      | ~ r2_hidden(A_164,C_163)
      | ~ r2_hidden(A_161,k1_tarski(A_164)) ) ),
    inference(resolution,[status(thm)],[c_156,c_377])).

tff(c_666,plain,(
    ! [A_168,B_169] :
      ( r2_hidden('#skF_1'(k1_tarski(A_168),B_169),'#skF_5')
      | r1_tarski(k1_tarski(A_168),B_169)
      | ~ r2_hidden(A_168,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_34,c_598])).

tff(c_683,plain,(
    ! [A_170] :
      ( r1_tarski(k1_tarski(A_170),'#skF_5')
      | ~ r2_hidden(A_170,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_666,c_4])).

tff(c_712,plain,(
    r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_92,c_683])).

tff(c_769,plain,(
    ! [B_173] :
      ( r1_tarski(k1_tarski('#skF_1'(k1_tarski('#skF_6'),B_173)),'#skF_5')
      | r1_tarski(k1_tarski('#skF_6'),B_173) ) ),
    inference(resolution,[status(thm)],[c_6,c_683])).

tff(c_87,plain,(
    ! [A_6,C_61] :
      ( r2_hidden(A_6,C_61)
      | ~ r1_tarski(k1_tarski(A_6),C_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_80])).

tff(c_816,plain,(
    ! [B_174] :
      ( r2_hidden('#skF_1'(k1_tarski('#skF_6'),B_174),'#skF_5')
      | r1_tarski(k1_tarski('#skF_6'),B_174) ) ),
    inference(resolution,[status(thm)],[c_769,c_87])).

tff(c_1102,plain,(
    ! [B_195,B_196] :
      ( r2_hidden('#skF_1'(k1_tarski('#skF_6'),B_195),B_196)
      | ~ r1_tarski('#skF_5',B_196)
      | r1_tarski(k1_tarski('#skF_6'),B_195) ) ),
    inference(resolution,[status(thm)],[c_816,c_2])).

tff(c_1131,plain,(
    ! [B_196] :
      ( ~ r1_tarski('#skF_5',B_196)
      | r1_tarski(k1_tarski('#skF_6'),B_196) ) ),
    inference(resolution,[status(thm)],[c_1102,c_4])).

tff(c_42,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_38,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_394,plain,(
    ! [A_125,B_126,C_127] :
      ( v3_pre_topc('#skF_2'(A_125,B_126,C_127),A_125)
      | ~ r1_tarski(C_127,B_126)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ v2_tex_2(B_126,A_125)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1418,plain,(
    ! [A_212,B_213,A_214] :
      ( v3_pre_topc('#skF_2'(A_212,B_213,A_214),A_212)
      | ~ r1_tarski(A_214,B_213)
      | ~ v2_tex_2(B_213,A_212)
      | ~ m1_subset_1(B_213,k1_zfmisc_1(u1_struct_0(A_212)))
      | ~ l1_pre_topc(A_212)
      | ~ r1_tarski(A_214,u1_struct_0(A_212)) ) ),
    inference(resolution,[status(thm)],[c_18,c_394])).

tff(c_1427,plain,(
    ! [A_214] :
      ( v3_pre_topc('#skF_2'('#skF_4','#skF_5',A_214),'#skF_4')
      | ~ r1_tarski(A_214,'#skF_5')
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_214,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_40,c_1418])).

tff(c_1433,plain,(
    ! [A_214] :
      ( v3_pre_topc('#skF_2'('#skF_4','#skF_5',A_214),'#skF_4')
      | ~ r1_tarski(A_214,'#skF_5')
      | ~ r1_tarski(A_214,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_1427])).

tff(c_835,plain,(
    ! [A_175,B_176,C_177] :
      ( k9_subset_1(u1_struct_0(A_175),B_176,'#skF_2'(A_175,B_176,C_177)) = C_177
      | ~ r1_tarski(C_177,B_176)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ v2_tex_2(B_176,A_175)
      | ~ m1_subset_1(B_176,k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ l1_pre_topc(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1980,plain,(
    ! [A_281,B_282,A_283] :
      ( k9_subset_1(u1_struct_0(A_281),B_282,'#skF_2'(A_281,B_282,A_283)) = A_283
      | ~ r1_tarski(A_283,B_282)
      | ~ v2_tex_2(B_282,A_281)
      | ~ m1_subset_1(B_282,k1_zfmisc_1(u1_struct_0(A_281)))
      | ~ l1_pre_topc(A_281)
      | ~ r1_tarski(A_283,u1_struct_0(A_281)) ) ),
    inference(resolution,[status(thm)],[c_18,c_835])).

tff(c_1989,plain,(
    ! [A_283] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_2'('#skF_4','#skF_5',A_283)) = A_283
      | ~ r1_tarski(A_283,'#skF_5')
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_283,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_40,c_1980])).

tff(c_1995,plain,(
    ! [A_283] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_2'('#skF_4','#skF_5',A_283)) = A_283
      | ~ r1_tarski(A_283,'#skF_5')
      | ~ r1_tarski(A_283,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_1989])).

tff(c_641,plain,(
    ! [A_165,B_166,C_167] :
      ( m1_subset_1('#skF_2'(A_165,B_166,C_167),k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ r1_tarski(C_167,B_166)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ v2_tex_2(B_166,A_165)
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ l1_pre_topc(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_32,plain,(
    ! [D_48] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',D_48) != k1_tarski('#skF_6')
      | ~ v3_pre_topc(D_48,'#skF_4')
      | ~ m1_subset_1(D_48,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_653,plain,(
    ! [B_166,C_167] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_2'('#skF_4',B_166,C_167)) != k1_tarski('#skF_6')
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_166,C_167),'#skF_4')
      | ~ r1_tarski(C_167,B_166)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_166,'#skF_4')
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_641,c_32])).

tff(c_2285,plain,(
    ! [B_327,C_328] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_2'('#skF_4',B_327,C_328)) != k1_tarski('#skF_6')
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_327,C_328),'#skF_4')
      | ~ r1_tarski(C_328,B_327)
      | ~ m1_subset_1(C_328,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_327,'#skF_4')
      | ~ m1_subset_1(B_327,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_653])).

tff(c_2287,plain,(
    ! [A_283] :
      ( k1_tarski('#skF_6') != A_283
      | ~ v3_pre_topc('#skF_2'('#skF_4','#skF_5',A_283),'#skF_4')
      | ~ r1_tarski(A_283,'#skF_5')
      | ~ m1_subset_1(A_283,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_283,'#skF_5')
      | ~ r1_tarski(A_283,u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1995,c_2285])).

tff(c_15069,plain,(
    ! [A_1520] :
      ( k1_tarski('#skF_6') != A_1520
      | ~ v3_pre_topc('#skF_2'('#skF_4','#skF_5',A_1520),'#skF_4')
      | ~ m1_subset_1(A_1520,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_1520,'#skF_5')
      | ~ r1_tarski(A_1520,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_2287])).

tff(c_15268,plain,(
    ! [A_1529] :
      ( k1_tarski('#skF_6') != A_1529
      | ~ v3_pre_topc('#skF_2'('#skF_4','#skF_5',A_1529),'#skF_4')
      | ~ r1_tarski(A_1529,'#skF_5')
      | ~ r1_tarski(A_1529,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_18,c_15069])).

tff(c_15309,plain,(
    ! [A_1532] :
      ( k1_tarski('#skF_6') != A_1532
      | ~ r1_tarski(A_1532,'#skF_5')
      | ~ r1_tarski(A_1532,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1433,c_15268])).

tff(c_15338,plain,
    ( ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5')
    | ~ r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1131,c_15309])).

tff(c_15395,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_712,c_15338])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:29:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.97/4.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.97/4.80  
% 10.97/4.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.97/4.80  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_1
% 10.97/4.80  
% 10.97/4.80  %Foreground sorts:
% 10.97/4.80  
% 10.97/4.80  
% 10.97/4.80  %Background operators:
% 10.97/4.80  
% 10.97/4.80  
% 10.97/4.80  %Foreground operators:
% 10.97/4.80  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 10.97/4.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.97/4.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.97/4.80  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.97/4.80  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.97/4.80  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.97/4.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.97/4.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.97/4.80  tff('#skF_5', type, '#skF_5': $i).
% 10.97/4.80  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 10.97/4.80  tff('#skF_6', type, '#skF_6': $i).
% 10.97/4.80  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.97/4.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.97/4.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.97/4.80  tff('#skF_4', type, '#skF_4': $i).
% 10.97/4.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.97/4.80  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.97/4.80  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.97/4.80  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 10.97/4.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.97/4.80  
% 10.97/4.82  tff(f_87, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_tex_2)).
% 10.97/4.82  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.97/4.82  tff(f_34, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 10.97/4.82  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 10.97/4.82  tff(f_40, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 10.97/4.82  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 10.97/4.82  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.97/4.82  tff(c_52, plain, (![A_50, B_51]: (r1_tarski(A_50, B_51) | ~m1_subset_1(A_50, k1_zfmisc_1(B_51)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.97/4.82  tff(c_56, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_52])).
% 10.97/4.82  tff(c_8, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.97/4.82  tff(c_73, plain, (![A_57, B_58]: (r2_hidden('#skF_1'(A_57, B_58), A_57) | r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.97/4.82  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.97/4.82  tff(c_78, plain, (![A_57]: (r1_tarski(A_57, A_57))), inference(resolution, [status(thm)], [c_73, c_4])).
% 10.97/4.82  tff(c_80, plain, (![B_60, C_61, A_62]: (r2_hidden(B_60, C_61) | ~r1_tarski(k2_tarski(A_62, B_60), C_61))), inference(cnfTransformation, [status(thm)], [f_40])).
% 10.97/4.82  tff(c_89, plain, (![B_63, A_64]: (r2_hidden(B_63, k2_tarski(A_64, B_63)))), inference(resolution, [status(thm)], [c_78, c_80])).
% 10.97/4.82  tff(c_92, plain, (![A_6]: (r2_hidden(A_6, k1_tarski(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_89])).
% 10.97/4.82  tff(c_34, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.97/4.82  tff(c_145, plain, (![A_79, B_80, C_81]: (r1_tarski(k2_tarski(A_79, B_80), C_81) | ~r2_hidden(B_80, C_81) | ~r2_hidden(A_79, C_81))), inference(cnfTransformation, [status(thm)], [f_40])).
% 10.97/4.82  tff(c_156, plain, (![A_6, C_81]: (r1_tarski(k1_tarski(A_6), C_81) | ~r2_hidden(A_6, C_81) | ~r2_hidden(A_6, C_81))), inference(superposition, [status(thm), theory('equality')], [c_8, c_145])).
% 10.97/4.82  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.97/4.82  tff(c_116, plain, (![C_73, B_74, A_75]: (r2_hidden(C_73, B_74) | ~r2_hidden(C_73, A_75) | ~r1_tarski(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.97/4.82  tff(c_199, plain, (![A_88, B_89, B_90]: (r2_hidden('#skF_1'(A_88, B_89), B_90) | ~r1_tarski(A_88, B_90) | r1_tarski(A_88, B_89))), inference(resolution, [status(thm)], [c_6, c_116])).
% 10.97/4.82  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.97/4.82  tff(c_209, plain, (![A_91, B_92, B_93, B_94]: (r2_hidden('#skF_1'(A_91, B_92), B_93) | ~r1_tarski(B_94, B_93) | ~r1_tarski(A_91, B_94) | r1_tarski(A_91, B_92))), inference(resolution, [status(thm)], [c_199, c_2])).
% 10.97/4.82  tff(c_377, plain, (![A_121, B_122, C_123, A_124]: (r2_hidden('#skF_1'(A_121, B_122), C_123) | ~r1_tarski(A_121, k1_tarski(A_124)) | r1_tarski(A_121, B_122) | ~r2_hidden(A_124, C_123))), inference(resolution, [status(thm)], [c_156, c_209])).
% 10.97/4.82  tff(c_598, plain, (![A_161, B_162, C_163, A_164]: (r2_hidden('#skF_1'(k1_tarski(A_161), B_162), C_163) | r1_tarski(k1_tarski(A_161), B_162) | ~r2_hidden(A_164, C_163) | ~r2_hidden(A_161, k1_tarski(A_164)))), inference(resolution, [status(thm)], [c_156, c_377])).
% 10.97/4.82  tff(c_666, plain, (![A_168, B_169]: (r2_hidden('#skF_1'(k1_tarski(A_168), B_169), '#skF_5') | r1_tarski(k1_tarski(A_168), B_169) | ~r2_hidden(A_168, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_34, c_598])).
% 10.97/4.82  tff(c_683, plain, (![A_170]: (r1_tarski(k1_tarski(A_170), '#skF_5') | ~r2_hidden(A_170, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_666, c_4])).
% 10.97/4.82  tff(c_712, plain, (r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_92, c_683])).
% 10.97/4.82  tff(c_769, plain, (![B_173]: (r1_tarski(k1_tarski('#skF_1'(k1_tarski('#skF_6'), B_173)), '#skF_5') | r1_tarski(k1_tarski('#skF_6'), B_173))), inference(resolution, [status(thm)], [c_6, c_683])).
% 10.97/4.82  tff(c_87, plain, (![A_6, C_61]: (r2_hidden(A_6, C_61) | ~r1_tarski(k1_tarski(A_6), C_61))), inference(superposition, [status(thm), theory('equality')], [c_8, c_80])).
% 10.97/4.82  tff(c_816, plain, (![B_174]: (r2_hidden('#skF_1'(k1_tarski('#skF_6'), B_174), '#skF_5') | r1_tarski(k1_tarski('#skF_6'), B_174))), inference(resolution, [status(thm)], [c_769, c_87])).
% 10.97/4.82  tff(c_1102, plain, (![B_195, B_196]: (r2_hidden('#skF_1'(k1_tarski('#skF_6'), B_195), B_196) | ~r1_tarski('#skF_5', B_196) | r1_tarski(k1_tarski('#skF_6'), B_195))), inference(resolution, [status(thm)], [c_816, c_2])).
% 10.97/4.82  tff(c_1131, plain, (![B_196]: (~r1_tarski('#skF_5', B_196) | r1_tarski(k1_tarski('#skF_6'), B_196))), inference(resolution, [status(thm)], [c_1102, c_4])).
% 10.97/4.82  tff(c_42, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.97/4.82  tff(c_38, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.97/4.82  tff(c_18, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.97/4.82  tff(c_394, plain, (![A_125, B_126, C_127]: (v3_pre_topc('#skF_2'(A_125, B_126, C_127), A_125) | ~r1_tarski(C_127, B_126) | ~m1_subset_1(C_127, k1_zfmisc_1(u1_struct_0(A_125))) | ~v2_tex_2(B_126, A_125) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.97/4.82  tff(c_1418, plain, (![A_212, B_213, A_214]: (v3_pre_topc('#skF_2'(A_212, B_213, A_214), A_212) | ~r1_tarski(A_214, B_213) | ~v2_tex_2(B_213, A_212) | ~m1_subset_1(B_213, k1_zfmisc_1(u1_struct_0(A_212))) | ~l1_pre_topc(A_212) | ~r1_tarski(A_214, u1_struct_0(A_212)))), inference(resolution, [status(thm)], [c_18, c_394])).
% 10.97/4.82  tff(c_1427, plain, (![A_214]: (v3_pre_topc('#skF_2'('#skF_4', '#skF_5', A_214), '#skF_4') | ~r1_tarski(A_214, '#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_214, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_40, c_1418])).
% 10.97/4.82  tff(c_1433, plain, (![A_214]: (v3_pre_topc('#skF_2'('#skF_4', '#skF_5', A_214), '#skF_4') | ~r1_tarski(A_214, '#skF_5') | ~r1_tarski(A_214, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_1427])).
% 10.97/4.82  tff(c_835, plain, (![A_175, B_176, C_177]: (k9_subset_1(u1_struct_0(A_175), B_176, '#skF_2'(A_175, B_176, C_177))=C_177 | ~r1_tarski(C_177, B_176) | ~m1_subset_1(C_177, k1_zfmisc_1(u1_struct_0(A_175))) | ~v2_tex_2(B_176, A_175) | ~m1_subset_1(B_176, k1_zfmisc_1(u1_struct_0(A_175))) | ~l1_pre_topc(A_175))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.97/4.82  tff(c_1980, plain, (![A_281, B_282, A_283]: (k9_subset_1(u1_struct_0(A_281), B_282, '#skF_2'(A_281, B_282, A_283))=A_283 | ~r1_tarski(A_283, B_282) | ~v2_tex_2(B_282, A_281) | ~m1_subset_1(B_282, k1_zfmisc_1(u1_struct_0(A_281))) | ~l1_pre_topc(A_281) | ~r1_tarski(A_283, u1_struct_0(A_281)))), inference(resolution, [status(thm)], [c_18, c_835])).
% 10.97/4.82  tff(c_1989, plain, (![A_283]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_2'('#skF_4', '#skF_5', A_283))=A_283 | ~r1_tarski(A_283, '#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_283, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_40, c_1980])).
% 10.97/4.82  tff(c_1995, plain, (![A_283]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_2'('#skF_4', '#skF_5', A_283))=A_283 | ~r1_tarski(A_283, '#skF_5') | ~r1_tarski(A_283, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_1989])).
% 10.97/4.82  tff(c_641, plain, (![A_165, B_166, C_167]: (m1_subset_1('#skF_2'(A_165, B_166, C_167), k1_zfmisc_1(u1_struct_0(A_165))) | ~r1_tarski(C_167, B_166) | ~m1_subset_1(C_167, k1_zfmisc_1(u1_struct_0(A_165))) | ~v2_tex_2(B_166, A_165) | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0(A_165))) | ~l1_pre_topc(A_165))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.97/4.82  tff(c_32, plain, (![D_48]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', D_48)!=k1_tarski('#skF_6') | ~v3_pre_topc(D_48, '#skF_4') | ~m1_subset_1(D_48, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.97/4.82  tff(c_653, plain, (![B_166, C_167]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_2'('#skF_4', B_166, C_167))!=k1_tarski('#skF_6') | ~v3_pre_topc('#skF_2'('#skF_4', B_166, C_167), '#skF_4') | ~r1_tarski(C_167, B_166) | ~m1_subset_1(C_167, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_166, '#skF_4') | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_641, c_32])).
% 10.97/4.82  tff(c_2285, plain, (![B_327, C_328]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_2'('#skF_4', B_327, C_328))!=k1_tarski('#skF_6') | ~v3_pre_topc('#skF_2'('#skF_4', B_327, C_328), '#skF_4') | ~r1_tarski(C_328, B_327) | ~m1_subset_1(C_328, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_327, '#skF_4') | ~m1_subset_1(B_327, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_653])).
% 10.97/4.82  tff(c_2287, plain, (![A_283]: (k1_tarski('#skF_6')!=A_283 | ~v3_pre_topc('#skF_2'('#skF_4', '#skF_5', A_283), '#skF_4') | ~r1_tarski(A_283, '#skF_5') | ~m1_subset_1(A_283, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_283, '#skF_5') | ~r1_tarski(A_283, u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1995, c_2285])).
% 10.97/4.82  tff(c_15069, plain, (![A_1520]: (k1_tarski('#skF_6')!=A_1520 | ~v3_pre_topc('#skF_2'('#skF_4', '#skF_5', A_1520), '#skF_4') | ~m1_subset_1(A_1520, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_1520, '#skF_5') | ~r1_tarski(A_1520, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_2287])).
% 10.97/4.82  tff(c_15268, plain, (![A_1529]: (k1_tarski('#skF_6')!=A_1529 | ~v3_pre_topc('#skF_2'('#skF_4', '#skF_5', A_1529), '#skF_4') | ~r1_tarski(A_1529, '#skF_5') | ~r1_tarski(A_1529, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_18, c_15069])).
% 10.97/4.82  tff(c_15309, plain, (![A_1532]: (k1_tarski('#skF_6')!=A_1532 | ~r1_tarski(A_1532, '#skF_5') | ~r1_tarski(A_1532, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1433, c_15268])).
% 10.97/4.82  tff(c_15338, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5') | ~r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1131, c_15309])).
% 10.97/4.82  tff(c_15395, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_712, c_15338])).
% 10.97/4.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.97/4.82  
% 10.97/4.82  Inference rules
% 10.97/4.82  ----------------------
% 10.97/4.82  #Ref     : 0
% 10.97/4.82  #Sup     : 3839
% 10.97/4.82  #Fact    : 0
% 10.97/4.82  #Define  : 0
% 10.97/4.82  #Split   : 21
% 10.97/4.82  #Chain   : 0
% 10.97/4.82  #Close   : 0
% 10.97/4.82  
% 10.97/4.82  Ordering : KBO
% 10.97/4.82  
% 10.97/4.82  Simplification rules
% 10.97/4.82  ----------------------
% 10.97/4.82  #Subsume      : 1834
% 10.97/4.82  #Demod        : 816
% 10.97/4.82  #Tautology    : 527
% 10.97/4.82  #SimpNegUnit  : 15
% 10.97/4.82  #BackRed      : 15
% 10.97/4.82  
% 10.97/4.82  #Partial instantiations: 0
% 10.97/4.82  #Strategies tried      : 1
% 10.97/4.82  
% 10.97/4.82  Timing (in seconds)
% 10.97/4.82  ----------------------
% 10.97/4.82  Preprocessing        : 0.28
% 10.97/4.82  Parsing              : 0.14
% 10.97/4.82  CNF conversion       : 0.02
% 10.97/4.82  Main loop            : 3.64
% 10.97/4.82  Inferencing          : 0.80
% 10.97/4.82  Reduction            : 0.84
% 10.97/4.82  Demodulation         : 0.56
% 10.97/4.82  BG Simplification    : 0.07
% 10.97/4.82  Subsumption          : 1.73
% 10.97/4.82  Abstraction          : 0.10
% 10.97/4.82  MUC search           : 0.00
% 10.97/4.82  Cooper               : 0.00
% 10.97/4.82  Total                : 3.96
% 10.97/4.82  Index Insertion      : 0.00
% 10.97/4.82  Index Deletion       : 0.00
% 10.97/4.82  Index Matching       : 0.00
% 10.97/4.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------

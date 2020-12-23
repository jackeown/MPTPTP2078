%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:21 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :   59 (  98 expanded)
%              Number of leaves         :   25 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  142 ( 296 expanded)
%              Number of equality atoms :   17 (  33 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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
                         => ~ ( v4_pre_topc(D,A)
                              & k9_subset_1(u1_struct_0(A),B,D) = k1_tarski(C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tex_2)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

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
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

tff(c_30,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_91,plain,(
    ! [A_66,B_67,C_68] :
      ( r1_tarski(k2_tarski(A_66,B_67),C_68)
      | ~ r2_hidden(B_67,C_68)
      | ~ r2_hidden(A_66,C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_100,plain,(
    ! [A_1,C_68] :
      ( r1_tarski(k1_tarski(A_1),C_68)
      | ~ r2_hidden(A_1,C_68)
      | ~ r2_hidden(A_1,C_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_91])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_48,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_52,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_48])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_77,plain,(
    ! [C_62,A_63,B_64] :
      ( r2_hidden(C_62,A_63)
      | ~ r2_hidden(C_62,B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_81,plain,(
    ! [A_65] :
      ( r2_hidden('#skF_5',A_65)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_65)) ) ),
    inference(resolution,[status(thm)],[c_30,c_77])).

tff(c_89,plain,(
    ! [B_10] :
      ( r2_hidden('#skF_5',B_10)
      | ~ r1_tarski('#skF_4',B_10) ) ),
    inference(resolution,[status(thm)],[c_14,c_81])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_34,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_236,plain,(
    ! [A_95,B_96,C_97] :
      ( v4_pre_topc('#skF_1'(A_95,B_96,C_97),A_95)
      | ~ r1_tarski(C_97,B_96)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ v2_tex_2(B_96,A_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_272,plain,(
    ! [A_102,B_103,A_104] :
      ( v4_pre_topc('#skF_1'(A_102,B_103,A_104),A_102)
      | ~ r1_tarski(A_104,B_103)
      | ~ v2_tex_2(B_103,A_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102)
      | ~ r1_tarski(A_104,u1_struct_0(A_102)) ) ),
    inference(resolution,[status(thm)],[c_14,c_236])).

tff(c_281,plain,(
    ! [A_102,A_9,A_104] :
      ( v4_pre_topc('#skF_1'(A_102,A_9,A_104),A_102)
      | ~ r1_tarski(A_104,A_9)
      | ~ v2_tex_2(A_9,A_102)
      | ~ l1_pre_topc(A_102)
      | ~ r1_tarski(A_104,u1_struct_0(A_102))
      | ~ r1_tarski(A_9,u1_struct_0(A_102)) ) ),
    inference(resolution,[status(thm)],[c_14,c_272])).

tff(c_343,plain,(
    ! [A_125,B_126,C_127] :
      ( k9_subset_1(u1_struct_0(A_125),B_126,'#skF_1'(A_125,B_126,C_127)) = C_127
      | ~ r1_tarski(C_127,B_126)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ v2_tex_2(B_126,A_125)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_381,plain,(
    ! [A_129,B_130,A_131] :
      ( k9_subset_1(u1_struct_0(A_129),B_130,'#skF_1'(A_129,B_130,A_131)) = A_131
      | ~ r1_tarski(A_131,B_130)
      | ~ v2_tex_2(B_130,A_129)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129)
      | ~ r1_tarski(A_131,u1_struct_0(A_129)) ) ),
    inference(resolution,[status(thm)],[c_14,c_343])).

tff(c_390,plain,(
    ! [A_131] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3','#skF_4',A_131)) = A_131
      | ~ r1_tarski(A_131,'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_131,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_36,c_381])).

tff(c_397,plain,(
    ! [A_132] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3','#skF_4',A_132)) = A_132
      | ~ r1_tarski(A_132,'#skF_4')
      | ~ r1_tarski(A_132,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_390])).

tff(c_286,plain,(
    ! [A_106,B_107,C_108] :
      ( m1_subset_1('#skF_1'(A_106,B_107,C_108),k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ r1_tarski(C_108,B_107)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ v2_tex_2(B_107,A_106)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_28,plain,(
    ! [D_47] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',D_47) != k1_tarski('#skF_5')
      | ~ v4_pre_topc(D_47,'#skF_3')
      | ~ m1_subset_1(D_47,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_310,plain,(
    ! [B_107,C_108] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_107,C_108)) != k1_tarski('#skF_5')
      | ~ v4_pre_topc('#skF_1'('#skF_3',B_107,C_108),'#skF_3')
      | ~ r1_tarski(C_108,B_107)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_107,'#skF_3')
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_286,c_28])).

tff(c_327,plain,(
    ! [B_107,C_108] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_107,C_108)) != k1_tarski('#skF_5')
      | ~ v4_pre_topc('#skF_1'('#skF_3',B_107,C_108),'#skF_3')
      | ~ r1_tarski(C_108,B_107)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_107,'#skF_3')
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_310])).

tff(c_404,plain,(
    ! [A_132] :
      ( k1_tarski('#skF_5') != A_132
      | ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4',A_132),'#skF_3')
      | ~ r1_tarski(A_132,'#skF_4')
      | ~ m1_subset_1(A_132,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_132,'#skF_4')
      | ~ r1_tarski(A_132,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_327])).

tff(c_445,plain,(
    ! [A_134] :
      ( k1_tarski('#skF_5') != A_134
      | ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4',A_134),'#skF_3')
      | ~ m1_subset_1(A_134,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_134,'#skF_4')
      | ~ r1_tarski(A_134,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_404])).

tff(c_472,plain,(
    ! [A_135] :
      ( k1_tarski('#skF_5') != A_135
      | ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4',A_135),'#skF_3')
      | ~ r1_tarski(A_135,'#skF_4')
      | ~ r1_tarski(A_135,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_14,c_445])).

tff(c_476,plain,(
    ! [A_104] :
      ( k1_tarski('#skF_5') != A_104
      | ~ r1_tarski(A_104,'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_104,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_4',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_281,c_472])).

tff(c_492,plain,(
    ! [A_136] :
      ( k1_tarski('#skF_5') != A_136
      | ~ r1_tarski(A_136,'#skF_4')
      | ~ r1_tarski(A_136,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_38,c_34,c_476])).

tff(c_526,plain,(
    ! [A_137] :
      ( k1_tarski(A_137) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_137),'#skF_4')
      | ~ r2_hidden(A_137,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_100,c_492])).

tff(c_530,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4')
    | ~ r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_89,c_526])).

tff(c_536,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_530])).

tff(c_540,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_536])).

tff(c_544,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_540])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:07:09 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.42  
% 2.95/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.43  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.95/1.43  
% 2.95/1.43  %Foreground sorts:
% 2.95/1.43  
% 2.95/1.43  
% 2.95/1.43  %Background operators:
% 2.95/1.43  
% 2.95/1.43  
% 2.95/1.43  %Foreground operators:
% 2.95/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.95/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.95/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.95/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.95/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.95/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.95/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.95/1.43  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.95/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.95/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.95/1.43  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.95/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.95/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.95/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.95/1.43  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.95/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.95/1.43  
% 2.95/1.44  tff(f_87, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tex_2)).
% 2.95/1.44  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.95/1.44  tff(f_33, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.95/1.44  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.95/1.44  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.95/1.44  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tex_2)).
% 2.95/1.44  tff(c_30, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.95/1.44  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.95/1.44  tff(c_91, plain, (![A_66, B_67, C_68]: (r1_tarski(k2_tarski(A_66, B_67), C_68) | ~r2_hidden(B_67, C_68) | ~r2_hidden(A_66, C_68))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.95/1.44  tff(c_100, plain, (![A_1, C_68]: (r1_tarski(k1_tarski(A_1), C_68) | ~r2_hidden(A_1, C_68) | ~r2_hidden(A_1, C_68))), inference(superposition, [status(thm), theory('equality')], [c_2, c_91])).
% 2.95/1.44  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.95/1.44  tff(c_48, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.95/1.44  tff(c_52, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_48])).
% 2.95/1.44  tff(c_14, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.95/1.44  tff(c_77, plain, (![C_62, A_63, B_64]: (r2_hidden(C_62, A_63) | ~r2_hidden(C_62, B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.95/1.44  tff(c_81, plain, (![A_65]: (r2_hidden('#skF_5', A_65) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_65)))), inference(resolution, [status(thm)], [c_30, c_77])).
% 2.95/1.44  tff(c_89, plain, (![B_10]: (r2_hidden('#skF_5', B_10) | ~r1_tarski('#skF_4', B_10))), inference(resolution, [status(thm)], [c_14, c_81])).
% 2.95/1.44  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.95/1.44  tff(c_34, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.95/1.44  tff(c_236, plain, (![A_95, B_96, C_97]: (v4_pre_topc('#skF_1'(A_95, B_96, C_97), A_95) | ~r1_tarski(C_97, B_96) | ~m1_subset_1(C_97, k1_zfmisc_1(u1_struct_0(A_95))) | ~v2_tex_2(B_96, A_95) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.95/1.44  tff(c_272, plain, (![A_102, B_103, A_104]: (v4_pre_topc('#skF_1'(A_102, B_103, A_104), A_102) | ~r1_tarski(A_104, B_103) | ~v2_tex_2(B_103, A_102) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102) | ~r1_tarski(A_104, u1_struct_0(A_102)))), inference(resolution, [status(thm)], [c_14, c_236])).
% 2.95/1.44  tff(c_281, plain, (![A_102, A_9, A_104]: (v4_pre_topc('#skF_1'(A_102, A_9, A_104), A_102) | ~r1_tarski(A_104, A_9) | ~v2_tex_2(A_9, A_102) | ~l1_pre_topc(A_102) | ~r1_tarski(A_104, u1_struct_0(A_102)) | ~r1_tarski(A_9, u1_struct_0(A_102)))), inference(resolution, [status(thm)], [c_14, c_272])).
% 2.95/1.44  tff(c_343, plain, (![A_125, B_126, C_127]: (k9_subset_1(u1_struct_0(A_125), B_126, '#skF_1'(A_125, B_126, C_127))=C_127 | ~r1_tarski(C_127, B_126) | ~m1_subset_1(C_127, k1_zfmisc_1(u1_struct_0(A_125))) | ~v2_tex_2(B_126, A_125) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.95/1.44  tff(c_381, plain, (![A_129, B_130, A_131]: (k9_subset_1(u1_struct_0(A_129), B_130, '#skF_1'(A_129, B_130, A_131))=A_131 | ~r1_tarski(A_131, B_130) | ~v2_tex_2(B_130, A_129) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129) | ~r1_tarski(A_131, u1_struct_0(A_129)))), inference(resolution, [status(thm)], [c_14, c_343])).
% 2.95/1.44  tff(c_390, plain, (![A_131]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', '#skF_4', A_131))=A_131 | ~r1_tarski(A_131, '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_131, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_36, c_381])).
% 2.95/1.44  tff(c_397, plain, (![A_132]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', '#skF_4', A_132))=A_132 | ~r1_tarski(A_132, '#skF_4') | ~r1_tarski(A_132, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_390])).
% 2.95/1.44  tff(c_286, plain, (![A_106, B_107, C_108]: (m1_subset_1('#skF_1'(A_106, B_107, C_108), k1_zfmisc_1(u1_struct_0(A_106))) | ~r1_tarski(C_108, B_107) | ~m1_subset_1(C_108, k1_zfmisc_1(u1_struct_0(A_106))) | ~v2_tex_2(B_107, A_106) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.95/1.44  tff(c_28, plain, (![D_47]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', D_47)!=k1_tarski('#skF_5') | ~v4_pre_topc(D_47, '#skF_3') | ~m1_subset_1(D_47, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.95/1.44  tff(c_310, plain, (![B_107, C_108]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_107, C_108))!=k1_tarski('#skF_5') | ~v4_pre_topc('#skF_1'('#skF_3', B_107, C_108), '#skF_3') | ~r1_tarski(C_108, B_107) | ~m1_subset_1(C_108, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_107, '#skF_3') | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_286, c_28])).
% 2.95/1.44  tff(c_327, plain, (![B_107, C_108]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_107, C_108))!=k1_tarski('#skF_5') | ~v4_pre_topc('#skF_1'('#skF_3', B_107, C_108), '#skF_3') | ~r1_tarski(C_108, B_107) | ~m1_subset_1(C_108, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_107, '#skF_3') | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_310])).
% 2.95/1.44  tff(c_404, plain, (![A_132]: (k1_tarski('#skF_5')!=A_132 | ~v4_pre_topc('#skF_1'('#skF_3', '#skF_4', A_132), '#skF_3') | ~r1_tarski(A_132, '#skF_4') | ~m1_subset_1(A_132, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_132, '#skF_4') | ~r1_tarski(A_132, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_397, c_327])).
% 2.95/1.44  tff(c_445, plain, (![A_134]: (k1_tarski('#skF_5')!=A_134 | ~v4_pre_topc('#skF_1'('#skF_3', '#skF_4', A_134), '#skF_3') | ~m1_subset_1(A_134, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_134, '#skF_4') | ~r1_tarski(A_134, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_404])).
% 2.95/1.44  tff(c_472, plain, (![A_135]: (k1_tarski('#skF_5')!=A_135 | ~v4_pre_topc('#skF_1'('#skF_3', '#skF_4', A_135), '#skF_3') | ~r1_tarski(A_135, '#skF_4') | ~r1_tarski(A_135, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_14, c_445])).
% 2.95/1.44  tff(c_476, plain, (![A_104]: (k1_tarski('#skF_5')!=A_104 | ~r1_tarski(A_104, '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_104, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_4', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_281, c_472])).
% 2.95/1.44  tff(c_492, plain, (![A_136]: (k1_tarski('#skF_5')!=A_136 | ~r1_tarski(A_136, '#skF_4') | ~r1_tarski(A_136, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_38, c_34, c_476])).
% 2.95/1.44  tff(c_526, plain, (![A_137]: (k1_tarski(A_137)!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_137), '#skF_4') | ~r2_hidden(A_137, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_100, c_492])).
% 2.95/1.44  tff(c_530, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4') | ~r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_89, c_526])).
% 2.95/1.44  tff(c_536, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_530])).
% 2.95/1.44  tff(c_540, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_100, c_536])).
% 2.95/1.44  tff(c_544, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_540])).
% 2.95/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.44  
% 2.95/1.44  Inference rules
% 2.95/1.44  ----------------------
% 2.95/1.44  #Ref     : 0
% 2.95/1.44  #Sup     : 96
% 2.95/1.44  #Fact    : 0
% 2.95/1.44  #Define  : 0
% 2.95/1.44  #Split   : 2
% 2.95/1.44  #Chain   : 0
% 2.95/1.44  #Close   : 0
% 2.95/1.44  
% 2.95/1.44  Ordering : KBO
% 2.95/1.44  
% 2.95/1.44  Simplification rules
% 2.95/1.44  ----------------------
% 2.95/1.44  #Subsume      : 16
% 2.95/1.44  #Demod        : 55
% 2.95/1.44  #Tautology    : 16
% 2.95/1.44  #SimpNegUnit  : 0
% 2.95/1.44  #BackRed      : 0
% 2.95/1.44  
% 2.95/1.44  #Partial instantiations: 0
% 2.95/1.44  #Strategies tried      : 1
% 2.95/1.44  
% 2.95/1.44  Timing (in seconds)
% 2.95/1.44  ----------------------
% 2.95/1.44  Preprocessing        : 0.31
% 2.95/1.44  Parsing              : 0.16
% 2.95/1.44  CNF conversion       : 0.02
% 2.95/1.44  Main loop            : 0.34
% 2.95/1.45  Inferencing          : 0.14
% 2.95/1.45  Reduction            : 0.09
% 2.95/1.45  Demodulation         : 0.06
% 2.95/1.45  BG Simplification    : 0.02
% 2.95/1.45  Subsumption          : 0.07
% 2.95/1.45  Abstraction          : 0.02
% 2.95/1.45  MUC search           : 0.00
% 2.95/1.45  Cooper               : 0.00
% 2.95/1.45  Total                : 0.68
% 2.95/1.45  Index Insertion      : 0.00
% 2.95/1.45  Index Deletion       : 0.00
% 3.07/1.45  Index Matching       : 0.00
% 3.07/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------

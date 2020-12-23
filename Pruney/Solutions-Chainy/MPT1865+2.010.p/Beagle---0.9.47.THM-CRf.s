%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:18 EST 2020

% Result     : Theorem 6.98s
% Output     : CNFRefutation 7.35s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 201 expanded)
%              Number of leaves         :   33 (  86 expanded)
%              Depth                    :   14
%              Number of atoms          :  183 ( 675 expanded)
%              Number of equality atoms :   19 (  69 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k1_enumset1 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
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

tff(f_49,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_51,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_36,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_91,axiom,(
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

tff(c_50,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_147,plain,(
    ! [B_76,A_77] :
      ( m1_subset_1(B_76,A_77)
      | ~ r2_hidden(B_76,A_77)
      | v1_xboole_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_159,plain,
    ( m1_subset_1('#skF_7','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_147])).

tff(c_160,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_26,plain,(
    ! [A_11] : k2_subset_1(A_11) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    ! [A_12] : m1_subset_1(k2_subset_1(A_12),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_59,plain,(
    ! [A_12] : m1_subset_1(A_12,k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28])).

tff(c_161,plain,(
    ! [C_78,B_79,A_80] :
      ( ~ v1_xboole_0(C_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(C_78))
      | ~ r2_hidden(A_80,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_175,plain,(
    ! [A_81,A_82] :
      ( ~ v1_xboole_0(A_81)
      | ~ r2_hidden(A_82,A_81) ) ),
    inference(resolution,[status(thm)],[c_59,c_161])).

tff(c_184,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_175])).

tff(c_190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_184])).

tff(c_192,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_52,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_30,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k1_tarski(A_13),k1_zfmisc_1(B_14))
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_141,plain,(
    ! [A_74,B_75] :
      ( r2_hidden(A_74,B_75)
      | v1_xboole_0(B_75)
      | ~ m1_subset_1(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6,plain,(
    ! [C_8,A_4] :
      ( r1_tarski(C_8,A_4)
      | ~ r2_hidden(C_8,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_241,plain,(
    ! [A_94,A_95] :
      ( r1_tarski(A_94,A_95)
      | v1_xboole_0(k1_zfmisc_1(A_95))
      | ~ m1_subset_1(A_94,k1_zfmisc_1(A_95)) ) ),
    inference(resolution,[status(thm)],[c_141,c_6])).

tff(c_255,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(k1_tarski(A_13),B_14)
      | v1_xboole_0(k1_zfmisc_1(B_14))
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(resolution,[status(thm)],[c_30,c_241])).

tff(c_95,plain,(
    ! [B_63,A_64] :
      ( v1_xboole_0(B_63)
      | ~ m1_subset_1(B_63,A_64)
      | ~ v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_110,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_52,c_95])).

tff(c_112,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_32,plain,(
    ! [A_15,B_16] :
      ( r2_hidden(A_15,B_16)
      | v1_xboole_0(B_16)
      | ~ m1_subset_1(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_58,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_54,plain,(
    v2_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1333,plain,(
    ! [A_157,B_158,C_159] :
      ( v4_pre_topc('#skF_3'(A_157,B_158,C_159),A_157)
      | ~ r1_tarski(C_159,B_158)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ v2_tex_2(B_158,A_157)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ l1_pre_topc(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1366,plain,(
    ! [A_157,B_158,A_13] :
      ( v4_pre_topc('#skF_3'(A_157,B_158,k1_tarski(A_13)),A_157)
      | ~ r1_tarski(k1_tarski(A_13),B_158)
      | ~ v2_tex_2(B_158,A_157)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ l1_pre_topc(A_157)
      | ~ r2_hidden(A_13,u1_struct_0(A_157)) ) ),
    inference(resolution,[status(thm)],[c_30,c_1333])).

tff(c_2346,plain,(
    ! [A_193,B_194,C_195] :
      ( k9_subset_1(u1_struct_0(A_193),B_194,'#skF_3'(A_193,B_194,C_195)) = C_195
      | ~ r1_tarski(C_195,B_194)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ v2_tex_2(B_194,A_193)
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ l1_pre_topc(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4652,plain,(
    ! [A_305,B_306,A_307] :
      ( k9_subset_1(u1_struct_0(A_305),B_306,'#skF_3'(A_305,B_306,k1_tarski(A_307))) = k1_tarski(A_307)
      | ~ r1_tarski(k1_tarski(A_307),B_306)
      | ~ v2_tex_2(B_306,A_305)
      | ~ m1_subset_1(B_306,k1_zfmisc_1(u1_struct_0(A_305)))
      | ~ l1_pre_topc(A_305)
      | ~ r2_hidden(A_307,u1_struct_0(A_305)) ) ),
    inference(resolution,[status(thm)],[c_30,c_2346])).

tff(c_1496,plain,(
    ! [A_166,B_167,C_168] :
      ( m1_subset_1('#skF_3'(A_166,B_167,C_168),k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ r1_tarski(C_168,B_167)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ v2_tex_2(B_167,A_166)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ l1_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_48,plain,(
    ! [D_56] :
      ( k9_subset_1(u1_struct_0('#skF_5'),'#skF_6',D_56) != k1_tarski('#skF_7')
      | ~ v4_pre_topc(D_56,'#skF_5')
      | ~ m1_subset_1(D_56,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1520,plain,(
    ! [B_167,C_168] :
      ( k9_subset_1(u1_struct_0('#skF_5'),'#skF_6','#skF_3'('#skF_5',B_167,C_168)) != k1_tarski('#skF_7')
      | ~ v4_pre_topc('#skF_3'('#skF_5',B_167,C_168),'#skF_5')
      | ~ r1_tarski(C_168,B_167)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v2_tex_2(B_167,'#skF_5')
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1496,c_48])).

tff(c_1540,plain,(
    ! [B_167,C_168] :
      ( k9_subset_1(u1_struct_0('#skF_5'),'#skF_6','#skF_3'('#skF_5',B_167,C_168)) != k1_tarski('#skF_7')
      | ~ v4_pre_topc('#skF_3'('#skF_5',B_167,C_168),'#skF_5')
      | ~ r1_tarski(C_168,B_167)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v2_tex_2(B_167,'#skF_5')
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1520])).

tff(c_4658,plain,(
    ! [A_307] :
      ( k1_tarski(A_307) != k1_tarski('#skF_7')
      | ~ v4_pre_topc('#skF_3'('#skF_5','#skF_6',k1_tarski(A_307)),'#skF_5')
      | ~ r1_tarski(k1_tarski(A_307),'#skF_6')
      | ~ m1_subset_1(k1_tarski(A_307),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v2_tex_2('#skF_6','#skF_5')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_tarski(k1_tarski(A_307),'#skF_6')
      | ~ v2_tex_2('#skF_6','#skF_5')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ r2_hidden(A_307,u1_struct_0('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4652,c_1540])).

tff(c_4981,plain,(
    ! [A_364] :
      ( k1_tarski(A_364) != k1_tarski('#skF_7')
      | ~ v4_pre_topc('#skF_3'('#skF_5','#skF_6',k1_tarski(A_364)),'#skF_5')
      | ~ m1_subset_1(k1_tarski(A_364),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_tarski(k1_tarski(A_364),'#skF_6')
      | ~ r2_hidden(A_364,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_56,c_54,c_4658])).

tff(c_4997,plain,(
    ! [A_365] :
      ( k1_tarski(A_365) != k1_tarski('#skF_7')
      | ~ v4_pre_topc('#skF_3'('#skF_5','#skF_6',k1_tarski(A_365)),'#skF_5')
      | ~ r1_tarski(k1_tarski(A_365),'#skF_6')
      | ~ r2_hidden(A_365,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_30,c_4981])).

tff(c_5001,plain,(
    ! [A_13] :
      ( k1_tarski(A_13) != k1_tarski('#skF_7')
      | ~ r1_tarski(k1_tarski(A_13),'#skF_6')
      | ~ v2_tex_2('#skF_6','#skF_5')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ r2_hidden(A_13,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1366,c_4997])).

tff(c_5005,plain,(
    ! [A_366] :
      ( k1_tarski(A_366) != k1_tarski('#skF_7')
      | ~ r1_tarski(k1_tarski(A_366),'#skF_6')
      | ~ r2_hidden(A_366,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_5001])).

tff(c_5017,plain,(
    ! [A_15] :
      ( k1_tarski(A_15) != k1_tarski('#skF_7')
      | ~ r1_tarski(k1_tarski(A_15),'#skF_6')
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_15,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_32,c_5005])).

tff(c_5023,plain,(
    ! [A_367] :
      ( k1_tarski(A_367) != k1_tarski('#skF_7')
      | ~ r1_tarski(k1_tarski(A_367),'#skF_6')
      | ~ m1_subset_1(A_367,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_5017])).

tff(c_5028,plain,(
    ! [A_13] :
      ( k1_tarski(A_13) != k1_tarski('#skF_7')
      | ~ m1_subset_1(A_13,u1_struct_0('#skF_5'))
      | v1_xboole_0(k1_zfmisc_1('#skF_6'))
      | ~ r2_hidden(A_13,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_255,c_5023])).

tff(c_5030,plain,(
    ! [A_368] :
      ( k1_tarski(A_368) != k1_tarski('#skF_7')
      | ~ m1_subset_1(A_368,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_368,'#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_5028])).

tff(c_5045,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_5030])).

tff(c_5056,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_5045])).

tff(c_5057,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_5028])).

tff(c_111,plain,(
    ! [A_12] :
      ( v1_xboole_0(A_12)
      | ~ v1_xboole_0(k1_zfmisc_1(A_12)) ) ),
    inference(resolution,[status(thm)],[c_59,c_95])).

tff(c_5064,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_5057,c_111])).

tff(c_5070,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_192,c_5064])).

tff(c_5072,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_5121,plain,(
    ! [C_382,B_383,A_384] :
      ( ~ v1_xboole_0(C_382)
      | ~ m1_subset_1(B_383,k1_zfmisc_1(C_382))
      | ~ r2_hidden(A_384,B_383) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_5128,plain,(
    ! [A_384] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_384,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_56,c_5121])).

tff(c_5135,plain,(
    ! [A_384] : ~ r2_hidden(A_384,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5072,c_5128])).

tff(c_5139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5135,c_50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:58:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.98/2.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.98/2.50  
% 6.98/2.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.98/2.51  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k1_enumset1 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_4
% 6.98/2.51  
% 6.98/2.51  %Foreground sorts:
% 6.98/2.51  
% 6.98/2.51  
% 6.98/2.51  %Background operators:
% 6.98/2.51  
% 6.98/2.51  
% 6.98/2.51  %Foreground operators:
% 6.98/2.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.98/2.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.98/2.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.98/2.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.98/2.51  tff('#skF_7', type, '#skF_7': $i).
% 6.98/2.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.98/2.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.98/2.51  tff('#skF_5', type, '#skF_5': $i).
% 6.98/2.51  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 6.98/2.51  tff('#skF_6', type, '#skF_6': $i).
% 6.98/2.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.98/2.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.98/2.51  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.98/2.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.98/2.51  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.98/2.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.98/2.51  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.98/2.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.98/2.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.98/2.51  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.98/2.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.98/2.51  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.98/2.51  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 6.98/2.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.98/2.51  
% 7.35/2.52  tff(f_113, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tex_2)).
% 7.35/2.52  tff(f_49, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 7.35/2.52  tff(f_51, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 7.35/2.52  tff(f_53, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 7.35/2.52  tff(f_70, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 7.35/2.52  tff(f_57, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 7.35/2.52  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 7.35/2.52  tff(f_36, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 7.35/2.52  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tex_2)).
% 7.35/2.52  tff(c_50, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.35/2.52  tff(c_147, plain, (![B_76, A_77]: (m1_subset_1(B_76, A_77) | ~r2_hidden(B_76, A_77) | v1_xboole_0(A_77))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.35/2.52  tff(c_159, plain, (m1_subset_1('#skF_7', '#skF_6') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_50, c_147])).
% 7.35/2.52  tff(c_160, plain, (v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_159])).
% 7.35/2.52  tff(c_26, plain, (![A_11]: (k2_subset_1(A_11)=A_11)), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.35/2.52  tff(c_28, plain, (![A_12]: (m1_subset_1(k2_subset_1(A_12), k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.35/2.52  tff(c_59, plain, (![A_12]: (m1_subset_1(A_12, k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28])).
% 7.35/2.52  tff(c_161, plain, (![C_78, B_79, A_80]: (~v1_xboole_0(C_78) | ~m1_subset_1(B_79, k1_zfmisc_1(C_78)) | ~r2_hidden(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.35/2.52  tff(c_175, plain, (![A_81, A_82]: (~v1_xboole_0(A_81) | ~r2_hidden(A_82, A_81))), inference(resolution, [status(thm)], [c_59, c_161])).
% 7.35/2.52  tff(c_184, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_50, c_175])).
% 7.35/2.52  tff(c_190, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_160, c_184])).
% 7.35/2.52  tff(c_192, plain, (~v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_159])).
% 7.35/2.52  tff(c_52, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.35/2.52  tff(c_30, plain, (![A_13, B_14]: (m1_subset_1(k1_tarski(A_13), k1_zfmisc_1(B_14)) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.35/2.52  tff(c_141, plain, (![A_74, B_75]: (r2_hidden(A_74, B_75) | v1_xboole_0(B_75) | ~m1_subset_1(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.35/2.52  tff(c_6, plain, (![C_8, A_4]: (r1_tarski(C_8, A_4) | ~r2_hidden(C_8, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.35/2.52  tff(c_241, plain, (![A_94, A_95]: (r1_tarski(A_94, A_95) | v1_xboole_0(k1_zfmisc_1(A_95)) | ~m1_subset_1(A_94, k1_zfmisc_1(A_95)))), inference(resolution, [status(thm)], [c_141, c_6])).
% 7.35/2.52  tff(c_255, plain, (![A_13, B_14]: (r1_tarski(k1_tarski(A_13), B_14) | v1_xboole_0(k1_zfmisc_1(B_14)) | ~r2_hidden(A_13, B_14))), inference(resolution, [status(thm)], [c_30, c_241])).
% 7.35/2.52  tff(c_95, plain, (![B_63, A_64]: (v1_xboole_0(B_63) | ~m1_subset_1(B_63, A_64) | ~v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.35/2.52  tff(c_110, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_52, c_95])).
% 7.35/2.52  tff(c_112, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_110])).
% 7.35/2.52  tff(c_32, plain, (![A_15, B_16]: (r2_hidden(A_15, B_16) | v1_xboole_0(B_16) | ~m1_subset_1(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.35/2.52  tff(c_58, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.35/2.52  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.35/2.52  tff(c_54, plain, (v2_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.35/2.52  tff(c_1333, plain, (![A_157, B_158, C_159]: (v4_pre_topc('#skF_3'(A_157, B_158, C_159), A_157) | ~r1_tarski(C_159, B_158) | ~m1_subset_1(C_159, k1_zfmisc_1(u1_struct_0(A_157))) | ~v2_tex_2(B_158, A_157) | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0(A_157))) | ~l1_pre_topc(A_157))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.35/2.52  tff(c_1366, plain, (![A_157, B_158, A_13]: (v4_pre_topc('#skF_3'(A_157, B_158, k1_tarski(A_13)), A_157) | ~r1_tarski(k1_tarski(A_13), B_158) | ~v2_tex_2(B_158, A_157) | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0(A_157))) | ~l1_pre_topc(A_157) | ~r2_hidden(A_13, u1_struct_0(A_157)))), inference(resolution, [status(thm)], [c_30, c_1333])).
% 7.35/2.52  tff(c_2346, plain, (![A_193, B_194, C_195]: (k9_subset_1(u1_struct_0(A_193), B_194, '#skF_3'(A_193, B_194, C_195))=C_195 | ~r1_tarski(C_195, B_194) | ~m1_subset_1(C_195, k1_zfmisc_1(u1_struct_0(A_193))) | ~v2_tex_2(B_194, A_193) | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0(A_193))) | ~l1_pre_topc(A_193))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.35/2.52  tff(c_4652, plain, (![A_305, B_306, A_307]: (k9_subset_1(u1_struct_0(A_305), B_306, '#skF_3'(A_305, B_306, k1_tarski(A_307)))=k1_tarski(A_307) | ~r1_tarski(k1_tarski(A_307), B_306) | ~v2_tex_2(B_306, A_305) | ~m1_subset_1(B_306, k1_zfmisc_1(u1_struct_0(A_305))) | ~l1_pre_topc(A_305) | ~r2_hidden(A_307, u1_struct_0(A_305)))), inference(resolution, [status(thm)], [c_30, c_2346])).
% 7.35/2.52  tff(c_1496, plain, (![A_166, B_167, C_168]: (m1_subset_1('#skF_3'(A_166, B_167, C_168), k1_zfmisc_1(u1_struct_0(A_166))) | ~r1_tarski(C_168, B_167) | ~m1_subset_1(C_168, k1_zfmisc_1(u1_struct_0(A_166))) | ~v2_tex_2(B_167, A_166) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0(A_166))) | ~l1_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.35/2.52  tff(c_48, plain, (![D_56]: (k9_subset_1(u1_struct_0('#skF_5'), '#skF_6', D_56)!=k1_tarski('#skF_7') | ~v4_pre_topc(D_56, '#skF_5') | ~m1_subset_1(D_56, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.35/2.52  tff(c_1520, plain, (![B_167, C_168]: (k9_subset_1(u1_struct_0('#skF_5'), '#skF_6', '#skF_3'('#skF_5', B_167, C_168))!=k1_tarski('#skF_7') | ~v4_pre_topc('#skF_3'('#skF_5', B_167, C_168), '#skF_5') | ~r1_tarski(C_168, B_167) | ~m1_subset_1(C_168, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v2_tex_2(B_167, '#skF_5') | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_1496, c_48])).
% 7.35/2.52  tff(c_1540, plain, (![B_167, C_168]: (k9_subset_1(u1_struct_0('#skF_5'), '#skF_6', '#skF_3'('#skF_5', B_167, C_168))!=k1_tarski('#skF_7') | ~v4_pre_topc('#skF_3'('#skF_5', B_167, C_168), '#skF_5') | ~r1_tarski(C_168, B_167) | ~m1_subset_1(C_168, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v2_tex_2(B_167, '#skF_5') | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1520])).
% 7.35/2.52  tff(c_4658, plain, (![A_307]: (k1_tarski(A_307)!=k1_tarski('#skF_7') | ~v4_pre_topc('#skF_3'('#skF_5', '#skF_6', k1_tarski(A_307)), '#skF_5') | ~r1_tarski(k1_tarski(A_307), '#skF_6') | ~m1_subset_1(k1_tarski(A_307), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v2_tex_2('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_tarski(k1_tarski(A_307), '#skF_6') | ~v2_tex_2('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~r2_hidden(A_307, u1_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_4652, c_1540])).
% 7.35/2.52  tff(c_4981, plain, (![A_364]: (k1_tarski(A_364)!=k1_tarski('#skF_7') | ~v4_pre_topc('#skF_3'('#skF_5', '#skF_6', k1_tarski(A_364)), '#skF_5') | ~m1_subset_1(k1_tarski(A_364), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_tarski(k1_tarski(A_364), '#skF_6') | ~r2_hidden(A_364, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_56, c_54, c_4658])).
% 7.35/2.52  tff(c_4997, plain, (![A_365]: (k1_tarski(A_365)!=k1_tarski('#skF_7') | ~v4_pre_topc('#skF_3'('#skF_5', '#skF_6', k1_tarski(A_365)), '#skF_5') | ~r1_tarski(k1_tarski(A_365), '#skF_6') | ~r2_hidden(A_365, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_30, c_4981])).
% 7.35/2.52  tff(c_5001, plain, (![A_13]: (k1_tarski(A_13)!=k1_tarski('#skF_7') | ~r1_tarski(k1_tarski(A_13), '#skF_6') | ~v2_tex_2('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~r2_hidden(A_13, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_1366, c_4997])).
% 7.35/2.52  tff(c_5005, plain, (![A_366]: (k1_tarski(A_366)!=k1_tarski('#skF_7') | ~r1_tarski(k1_tarski(A_366), '#skF_6') | ~r2_hidden(A_366, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_5001])).
% 7.35/2.52  tff(c_5017, plain, (![A_15]: (k1_tarski(A_15)!=k1_tarski('#skF_7') | ~r1_tarski(k1_tarski(A_15), '#skF_6') | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(A_15, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_32, c_5005])).
% 7.35/2.52  tff(c_5023, plain, (![A_367]: (k1_tarski(A_367)!=k1_tarski('#skF_7') | ~r1_tarski(k1_tarski(A_367), '#skF_6') | ~m1_subset_1(A_367, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_112, c_5017])).
% 7.35/2.52  tff(c_5028, plain, (![A_13]: (k1_tarski(A_13)!=k1_tarski('#skF_7') | ~m1_subset_1(A_13, u1_struct_0('#skF_5')) | v1_xboole_0(k1_zfmisc_1('#skF_6')) | ~r2_hidden(A_13, '#skF_6'))), inference(resolution, [status(thm)], [c_255, c_5023])).
% 7.35/2.52  tff(c_5030, plain, (![A_368]: (k1_tarski(A_368)!=k1_tarski('#skF_7') | ~m1_subset_1(A_368, u1_struct_0('#skF_5')) | ~r2_hidden(A_368, '#skF_6'))), inference(splitLeft, [status(thm)], [c_5028])).
% 7.35/2.52  tff(c_5045, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_52, c_5030])).
% 7.35/2.52  tff(c_5056, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_5045])).
% 7.35/2.52  tff(c_5057, plain, (v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(splitRight, [status(thm)], [c_5028])).
% 7.35/2.52  tff(c_111, plain, (![A_12]: (v1_xboole_0(A_12) | ~v1_xboole_0(k1_zfmisc_1(A_12)))), inference(resolution, [status(thm)], [c_59, c_95])).
% 7.35/2.52  tff(c_5064, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_5057, c_111])).
% 7.35/2.52  tff(c_5070, plain, $false, inference(negUnitSimplification, [status(thm)], [c_192, c_5064])).
% 7.35/2.52  tff(c_5072, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_110])).
% 7.35/2.52  tff(c_5121, plain, (![C_382, B_383, A_384]: (~v1_xboole_0(C_382) | ~m1_subset_1(B_383, k1_zfmisc_1(C_382)) | ~r2_hidden(A_384, B_383))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.35/2.52  tff(c_5128, plain, (![A_384]: (~v1_xboole_0(u1_struct_0('#skF_5')) | ~r2_hidden(A_384, '#skF_6'))), inference(resolution, [status(thm)], [c_56, c_5121])).
% 7.35/2.52  tff(c_5135, plain, (![A_384]: (~r2_hidden(A_384, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_5072, c_5128])).
% 7.35/2.52  tff(c_5139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5135, c_50])).
% 7.35/2.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.35/2.52  
% 7.35/2.52  Inference rules
% 7.35/2.52  ----------------------
% 7.35/2.52  #Ref     : 0
% 7.35/2.52  #Sup     : 1263
% 7.35/2.52  #Fact    : 8
% 7.35/2.52  #Define  : 0
% 7.35/2.52  #Split   : 23
% 7.35/2.52  #Chain   : 0
% 7.35/2.52  #Close   : 0
% 7.35/2.52  
% 7.35/2.52  Ordering : KBO
% 7.35/2.52  
% 7.35/2.52  Simplification rules
% 7.35/2.52  ----------------------
% 7.35/2.52  #Subsume      : 581
% 7.35/2.52  #Demod        : 433
% 7.35/2.52  #Tautology    : 346
% 7.35/2.52  #SimpNegUnit  : 46
% 7.35/2.52  #BackRed      : 1
% 7.35/2.52  
% 7.35/2.52  #Partial instantiations: 0
% 7.35/2.52  #Strategies tried      : 1
% 7.35/2.52  
% 7.35/2.52  Timing (in seconds)
% 7.35/2.52  ----------------------
% 7.35/2.53  Preprocessing        : 0.32
% 7.35/2.53  Parsing              : 0.16
% 7.35/2.53  CNF conversion       : 0.02
% 7.35/2.53  Main loop            : 1.37
% 7.35/2.53  Inferencing          : 0.43
% 7.35/2.53  Reduction            : 0.36
% 7.35/2.53  Demodulation         : 0.24
% 7.35/2.53  BG Simplification    : 0.06
% 7.35/2.53  Subsumption          : 0.42
% 7.35/2.53  Abstraction          : 0.07
% 7.35/2.53  MUC search           : 0.00
% 7.35/2.53  Cooper               : 0.00
% 7.35/2.53  Total                : 1.72
% 7.35/2.53  Index Insertion      : 0.00
% 7.35/2.53  Index Deletion       : 0.00
% 7.35/2.53  Index Matching       : 0.00
% 7.35/2.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------

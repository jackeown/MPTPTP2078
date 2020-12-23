%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT2062+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:49 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 113 expanded)
%              Number of leaves         :   25 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :  178 ( 365 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_7 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(r2_waybel_7,type,(
    r2_waybel_7: ( $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B,C,D] :
            ( ( r1_tarski(B,C)
              & r2_waybel_7(A,B,D) )
           => r2_waybel_7(A,C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_yellow19)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_40,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B,C] :
          ( r2_waybel_7(A,B,C)
        <=> ! [D] :
              ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(D,A)
                  & r2_hidden(C,D) )
               => r2_hidden(D,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_waybel_7)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(c_30,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_28,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_24,plain,(
    r2_waybel_7('#skF_2','#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22,plain,(
    ~ r2_waybel_7('#skF_2','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | v1_xboole_0(B_14)
      | ~ m1_subset_1(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_40,plain,(
    ! [C_32,B_33,A_34] :
      ( ~ v1_xboole_0(C_32)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(C_32))
      | ~ r2_hidden(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_44,plain,(
    ! [B_35,A_36,A_37] :
      ( ~ v1_xboole_0(B_35)
      | ~ r2_hidden(A_36,A_37)
      | ~ r1_tarski(A_37,B_35) ) ),
    inference(resolution,[status(thm)],[c_16,c_40])).

tff(c_56,plain,(
    ! [B_44,B_45,A_46] :
      ( ~ v1_xboole_0(B_44)
      | ~ r1_tarski(B_45,B_44)
      | v1_xboole_0(B_45)
      | ~ m1_subset_1(A_46,B_45) ) ),
    inference(resolution,[status(thm)],[c_12,c_44])).

tff(c_59,plain,(
    ! [A_46] :
      ( ~ v1_xboole_0('#skF_4')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_46,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_56])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_59])).

tff(c_8,plain,(
    ! [A_1,B_8,C_9] :
      ( v3_pre_topc('#skF_1'(A_1,B_8,C_9),A_1)
      | r2_waybel_7(A_1,B_8,C_9)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_10,plain,(
    ! [A_1,B_8,C_9] :
      ( m1_subset_1('#skF_1'(A_1,B_8,C_9),k1_zfmisc_1(u1_struct_0(A_1)))
      | r2_waybel_7(A_1,B_8,C_9)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6,plain,(
    ! [C_9,A_1,B_8] :
      ( r2_hidden(C_9,'#skF_1'(A_1,B_8,C_9))
      | r2_waybel_7(A_1,B_8,C_9)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_109,plain,(
    ! [D_68,B_69,C_70,A_71] :
      ( r2_hidden(D_68,B_69)
      | ~ r2_hidden(C_70,D_68)
      | ~ v3_pre_topc(D_68,A_71)
      | ~ m1_subset_1(D_68,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ r2_waybel_7(A_71,B_69,C_70)
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_212,plain,(
    ! [C_115,A_117,B_114,A_118,B_116] :
      ( r2_hidden('#skF_1'(A_118,B_114,C_115),B_116)
      | ~ v3_pre_topc('#skF_1'(A_118,B_114,C_115),A_117)
      | ~ m1_subset_1('#skF_1'(A_118,B_114,C_115),k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ r2_waybel_7(A_117,B_116,C_115)
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117)
      | r2_waybel_7(A_118,B_114,C_115)
      | ~ l1_pre_topc(A_118)
      | ~ v2_pre_topc(A_118) ) ),
    inference(resolution,[status(thm)],[c_6,c_109])).

tff(c_220,plain,(
    ! [A_119,B_120,C_121,B_122] :
      ( r2_hidden('#skF_1'(A_119,B_120,C_121),B_122)
      | ~ v3_pre_topc('#skF_1'(A_119,B_120,C_121),A_119)
      | ~ r2_waybel_7(A_119,B_122,C_121)
      | r2_waybel_7(A_119,B_120,C_121)
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119) ) ),
    inference(resolution,[status(thm)],[c_10,c_212])).

tff(c_224,plain,(
    ! [A_123,B_124,C_125,B_126] :
      ( r2_hidden('#skF_1'(A_123,B_124,C_125),B_126)
      | ~ r2_waybel_7(A_123,B_126,C_125)
      | r2_waybel_7(A_123,B_124,C_125)
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123) ) ),
    inference(resolution,[status(thm)],[c_8,c_220])).

tff(c_48,plain,(
    ! [A_38,C_39,B_40] :
      ( m1_subset_1(A_38,C_39)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(C_39))
      | ~ r2_hidden(A_38,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_51,plain,(
    ! [A_38,B_16,A_15] :
      ( m1_subset_1(A_38,B_16)
      | ~ r2_hidden(A_38,A_15)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(resolution,[status(thm)],[c_16,c_48])).

tff(c_287,plain,(
    ! [C_137,B_140,A_139,B_138,B_141] :
      ( m1_subset_1('#skF_1'(A_139,B_140,C_137),B_138)
      | ~ r1_tarski(B_141,B_138)
      | ~ r2_waybel_7(A_139,B_141,C_137)
      | r2_waybel_7(A_139,B_140,C_137)
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139) ) ),
    inference(resolution,[status(thm)],[c_224,c_51])).

tff(c_294,plain,(
    ! [A_142,B_143,C_144] :
      ( m1_subset_1('#skF_1'(A_142,B_143,C_144),'#skF_4')
      | ~ r2_waybel_7(A_142,'#skF_3',C_144)
      | r2_waybel_7(A_142,B_143,C_144)
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142) ) ),
    inference(resolution,[status(thm)],[c_26,c_287])).

tff(c_67,plain,(
    ! [A_53,B_54,C_55] :
      ( ~ r2_hidden('#skF_1'(A_53,B_54,C_55),B_54)
      | r2_waybel_7(A_53,B_54,C_55)
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_72,plain,(
    ! [A_53,B_14,C_55] :
      ( r2_waybel_7(A_53,B_14,C_55)
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53)
      | v1_xboole_0(B_14)
      | ~ m1_subset_1('#skF_1'(A_53,B_14,C_55),B_14) ) ),
    inference(resolution,[status(thm)],[c_12,c_67])).

tff(c_298,plain,(
    ! [A_142,C_144] :
      ( v1_xboole_0('#skF_4')
      | ~ r2_waybel_7(A_142,'#skF_3',C_144)
      | r2_waybel_7(A_142,'#skF_4',C_144)
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142) ) ),
    inference(resolution,[status(thm)],[c_294,c_72])).

tff(c_302,plain,(
    ! [A_145,C_146] :
      ( ~ r2_waybel_7(A_145,'#skF_3',C_146)
      | r2_waybel_7(A_145,'#skF_4',C_146)
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_298])).

tff(c_307,plain,
    ( r2_waybel_7('#skF_2','#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_302])).

tff(c_310,plain,(
    r2_waybel_7('#skF_2','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_307])).

tff(c_312,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_310])).

tff(c_314,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_59])).

tff(c_365,plain,(
    ! [D_171,B_172,C_173,A_174] :
      ( r2_hidden(D_171,B_172)
      | ~ r2_hidden(C_173,D_171)
      | ~ v3_pre_topc(D_171,A_174)
      | ~ m1_subset_1(D_171,k1_zfmisc_1(u1_struct_0(A_174)))
      | ~ r2_waybel_7(A_174,B_172,C_173)
      | ~ l1_pre_topc(A_174)
      | ~ v2_pre_topc(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_472,plain,(
    ! [B_221,B_217,A_220,C_218,A_219] :
      ( r2_hidden('#skF_1'(A_220,B_217,C_218),B_221)
      | ~ v3_pre_topc('#skF_1'(A_220,B_217,C_218),A_219)
      | ~ m1_subset_1('#skF_1'(A_220,B_217,C_218),k1_zfmisc_1(u1_struct_0(A_219)))
      | ~ r2_waybel_7(A_219,B_221,C_218)
      | ~ l1_pre_topc(A_219)
      | ~ v2_pre_topc(A_219)
      | r2_waybel_7(A_220,B_217,C_218)
      | ~ l1_pre_topc(A_220)
      | ~ v2_pre_topc(A_220) ) ),
    inference(resolution,[status(thm)],[c_6,c_365])).

tff(c_480,plain,(
    ! [A_222,B_223,C_224,B_225] :
      ( r2_hidden('#skF_1'(A_222,B_223,C_224),B_225)
      | ~ v3_pre_topc('#skF_1'(A_222,B_223,C_224),A_222)
      | ~ r2_waybel_7(A_222,B_225,C_224)
      | r2_waybel_7(A_222,B_223,C_224)
      | ~ l1_pre_topc(A_222)
      | ~ v2_pre_topc(A_222) ) ),
    inference(resolution,[status(thm)],[c_10,c_472])).

tff(c_484,plain,(
    ! [A_226,B_227,C_228,B_229] :
      ( r2_hidden('#skF_1'(A_226,B_227,C_228),B_229)
      | ~ r2_waybel_7(A_226,B_229,C_228)
      | r2_waybel_7(A_226,B_227,C_228)
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226) ) ),
    inference(resolution,[status(thm)],[c_8,c_480])).

tff(c_43,plain,(
    ! [B_16,A_34,A_15] :
      ( ~ v1_xboole_0(B_16)
      | ~ r2_hidden(A_34,A_15)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(resolution,[status(thm)],[c_16,c_40])).

tff(c_504,plain,(
    ! [B_234,A_233,B_231,C_232,B_230] :
      ( ~ v1_xboole_0(B_231)
      | ~ r1_tarski(B_234,B_231)
      | ~ r2_waybel_7(A_233,B_234,C_232)
      | r2_waybel_7(A_233,B_230,C_232)
      | ~ l1_pre_topc(A_233)
      | ~ v2_pre_topc(A_233) ) ),
    inference(resolution,[status(thm)],[c_484,c_43])).

tff(c_508,plain,(
    ! [A_233,C_232,B_230] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_waybel_7(A_233,'#skF_3',C_232)
      | r2_waybel_7(A_233,B_230,C_232)
      | ~ l1_pre_topc(A_233)
      | ~ v2_pre_topc(A_233) ) ),
    inference(resolution,[status(thm)],[c_26,c_504])).

tff(c_513,plain,(
    ! [A_235,C_236,B_237] :
      ( ~ r2_waybel_7(A_235,'#skF_3',C_236)
      | r2_waybel_7(A_235,B_237,C_236)
      | ~ l1_pre_topc(A_235)
      | ~ v2_pre_topc(A_235) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_508])).

tff(c_516,plain,(
    ! [B_237] :
      ( r2_waybel_7('#skF_2',B_237,'#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_513])).

tff(c_519,plain,(
    ! [B_237] : r2_waybel_7('#skF_2',B_237,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_516])).

tff(c_523,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_22])).

%------------------------------------------------------------------------------

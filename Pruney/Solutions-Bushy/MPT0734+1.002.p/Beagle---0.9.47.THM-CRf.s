%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0734+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:47 EST 2020

% Result     : Theorem 5.17s
% Output     : CNFRefutation 5.17s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 682 expanded)
%              Number of leaves         :   27 ( 240 expanded)
%              Depth                    :   18
%              Number of atoms          :  236 (1829 expanded)
%              Number of equality atoms :   19 (  51 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v3_ordinal1 > v2_ordinal1 > v1_xboole_0 > v1_ordinal1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( v1_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ! [C] :
                ( v3_ordinal1(C)
               => ( ( r1_tarski(A,B)
                    & r2_hidden(B,C) )
                 => r2_hidden(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_ordinal1)).

tff(f_30,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(c_40,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_42,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_58,plain,(
    ! [A_35] :
      ( v1_ordinal1(A_35)
      | ~ v3_ordinal1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_65,plain,(
    v1_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_58])).

tff(c_38,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_4441,plain,(
    ! [B_224,A_225] :
      ( r1_tarski(B_224,A_225)
      | ~ r2_hidden(B_224,A_225)
      | ~ v1_ordinal1(A_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4450,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ v1_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_4441])).

tff(c_4455,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_4450])).

tff(c_4475,plain,(
    ! [A_231,C_232,B_233] :
      ( r1_tarski(A_231,C_232)
      | ~ r1_tarski(B_233,C_232)
      | ~ r1_tarski(A_231,B_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4482,plain,(
    ! [A_231] :
      ( r1_tarski(A_231,'#skF_5')
      | ~ r1_tarski(A_231,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4455,c_4475])).

tff(c_46,plain,(
    v1_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r2_xboole_0(A_6,B_7)
      | B_7 = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4618,plain,(
    ! [A_254,B_255] :
      ( r2_hidden(A_254,B_255)
      | ~ r2_xboole_0(A_254,B_255)
      | ~ v3_ordinal1(B_255)
      | ~ v1_ordinal1(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4833,plain,(
    ! [A_271,B_272] :
      ( r2_hidden(A_271,B_272)
      | ~ v3_ordinal1(B_272)
      | ~ v1_ordinal1(A_271)
      | B_272 = A_271
      | ~ r1_tarski(A_271,B_272) ) ),
    inference(resolution,[status(thm)],[c_12,c_4618])).

tff(c_36,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_4851,plain,
    ( ~ v3_ordinal1('#skF_5')
    | ~ v1_ordinal1('#skF_3')
    | '#skF_5' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_4833,c_36])).

tff(c_4859,plain,
    ( '#skF_5' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_4851])).

tff(c_4860,plain,(
    ~ r1_tarski('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4859])).

tff(c_4866,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_4482,c_4860])).

tff(c_4873,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4866])).

tff(c_4874,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4859])).

tff(c_89,plain,(
    ! [B_49,A_50] :
      ( r1_tarski(B_49,A_50)
      | ~ r2_hidden(B_49,A_50)
      | ~ v1_ordinal1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_98,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ v1_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_89])).

tff(c_103,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_98])).

tff(c_134,plain,(
    ! [A_58,C_59,B_60] :
      ( r1_tarski(A_58,C_59)
      | ~ r1_tarski(B_60,C_59)
      | ~ r1_tarski(A_58,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_141,plain,(
    ! [A_58] :
      ( r1_tarski(A_58,'#skF_5')
      | ~ r1_tarski(A_58,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_103,c_134])).

tff(c_174,plain,(
    ! [A_67,B_68] :
      ( r2_hidden(A_67,B_68)
      | ~ r2_xboole_0(A_67,B_68)
      | ~ v3_ordinal1(B_68)
      | ~ v1_ordinal1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_550,plain,(
    ! [A_99,B_100] :
      ( r2_hidden(A_99,B_100)
      | ~ v3_ordinal1(B_100)
      | ~ v1_ordinal1(A_99)
      | B_100 = A_99
      | ~ r1_tarski(A_99,B_100) ) ),
    inference(resolution,[status(thm)],[c_12,c_174])).

tff(c_568,plain,
    ( ~ v3_ordinal1('#skF_5')
    | ~ v1_ordinal1('#skF_3')
    | '#skF_5' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_550,c_36])).

tff(c_576,plain,
    ( '#skF_5' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_568])).

tff(c_577,plain,(
    ~ r1_tarski('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_576])).

tff(c_589,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_141,c_577])).

tff(c_597,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_589])).

tff(c_598,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_576])).

tff(c_28,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_115,plain,(
    ! [C_53,B_54,A_55] :
      ( ~ v1_xboole_0(C_53)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(C_53))
      | ~ r2_hidden(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_164,plain,(
    ! [B_64,A_65,A_66] :
      ( ~ v1_xboole_0(B_64)
      | ~ r2_hidden(A_65,A_66)
      | ~ r1_tarski(A_66,B_64) ) ),
    inference(resolution,[status(thm)],[c_28,c_115])).

tff(c_179,plain,(
    ! [B_69] :
      ( ~ v1_xboole_0(B_69)
      | ~ r1_tarski('#skF_5',B_69) ) ),
    inference(resolution,[status(thm)],[c_38,c_164])).

tff(c_184,plain,
    ( ~ v1_xboole_0('#skF_5')
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_141,c_179])).

tff(c_185,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_606,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_598,c_185])).

tff(c_618,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_606])).

tff(c_620,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_628,plain,(
    ! [A_102,C_103,B_104] :
      ( m1_subset_1(A_102,C_103)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(C_103))
      | ~ r2_hidden(A_102,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_752,plain,(
    ! [A_114,B_115,A_116] :
      ( m1_subset_1(A_114,B_115)
      | ~ r2_hidden(A_114,A_116)
      | ~ r1_tarski(A_116,B_115) ) ),
    inference(resolution,[status(thm)],[c_28,c_628])).

tff(c_762,plain,(
    ! [B_117] :
      ( m1_subset_1('#skF_4',B_117)
      | ~ r1_tarski('#skF_5',B_117) ) ),
    inference(resolution,[status(thm)],[c_38,c_752])).

tff(c_770,plain,(
    m1_subset_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_620,c_762])).

tff(c_173,plain,(
    ! [B_64] :
      ( ~ v1_xboole_0(B_64)
      | ~ r1_tarski('#skF_5',B_64) ) ),
    inference(resolution,[status(thm)],[c_38,c_164])).

tff(c_626,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_620,c_173])).

tff(c_20,plain,(
    ! [A_10,C_12,B_11] :
      ( r1_tarski(A_10,C_12)
      | ~ r1_tarski(B_11,C_12)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_636,plain,(
    ! [A_105] :
      ( r1_tarski(A_105,'#skF_4')
      | ~ r1_tarski(A_105,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_620,c_20])).

tff(c_648,plain,(
    r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_103,c_636])).

tff(c_154,plain,(
    ! [A_63] :
      ( r1_tarski(A_63,'#skF_5')
      | ~ r1_tarski(A_63,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_103,c_134])).

tff(c_774,plain,(
    ! [A_118,A_119] :
      ( r1_tarski(A_118,'#skF_5')
      | ~ r1_tarski(A_118,A_119)
      | ~ r1_tarski(A_119,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_154,c_20])).

tff(c_794,plain,
    ( r1_tarski('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_774])).

tff(c_820,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_794])).

tff(c_1281,plain,(
    ! [A_138,B_139] :
      ( r2_hidden(A_138,B_139)
      | ~ v3_ordinal1(B_139)
      | ~ v1_ordinal1(A_138)
      | B_139 = A_138
      | ~ r1_tarski(A_138,B_139) ) ),
    inference(resolution,[status(thm)],[c_12,c_174])).

tff(c_1299,plain,
    ( ~ v3_ordinal1('#skF_5')
    | ~ v1_ordinal1('#skF_3')
    | '#skF_5' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_1281,c_36])).

tff(c_1307,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_820,c_46,c_42,c_1299])).

tff(c_83,plain,(
    ! [A_47,B_48] :
      ( r2_hidden(A_47,B_48)
      | v1_xboole_0(B_48)
      | ~ m1_subset_1(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_87,plain,
    ( v1_xboole_0('#skF_5')
    | ~ m1_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_83,c_36])).

tff(c_88,plain,(
    ~ m1_subset_1('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_1331,plain,(
    ~ m1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1307,c_88])).

tff(c_44,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_66,plain,(
    v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_58])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( r2_hidden(A_16,B_17)
      | v1_xboole_0(B_17)
      | ~ m1_subset_1(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_934,plain,(
    ! [A_121,B_122] :
      ( r1_tarski(A_121,B_122)
      | ~ v1_ordinal1(B_122)
      | v1_xboole_0(B_122)
      | ~ m1_subset_1(A_121,B_122) ) ),
    inference(resolution,[status(thm)],[c_24,c_89])).

tff(c_2914,plain,(
    ! [A_192,B_193,A_194] :
      ( r1_tarski(A_192,B_193)
      | ~ r1_tarski(A_192,A_194)
      | ~ v1_ordinal1(B_193)
      | v1_xboole_0(B_193)
      | ~ m1_subset_1(A_194,B_193) ) ),
    inference(resolution,[status(thm)],[c_934,c_20])).

tff(c_2992,plain,(
    ! [B_193] :
      ( r1_tarski('#skF_3',B_193)
      | ~ v1_ordinal1(B_193)
      | v1_xboole_0(B_193)
      | ~ m1_subset_1('#skF_4',B_193) ) ),
    inference(resolution,[status(thm)],[c_40,c_2914])).

tff(c_1330,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1307,c_103])).

tff(c_634,plain,(
    ! [A_102,B_19,A_18] :
      ( m1_subset_1(A_102,B_19)
      | ~ r2_hidden(A_102,A_18)
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(resolution,[status(thm)],[c_28,c_628])).

tff(c_3631,plain,(
    ! [A_208,B_209,B_210] :
      ( m1_subset_1(A_208,B_209)
      | ~ r1_tarski(B_210,B_209)
      | ~ v3_ordinal1(B_210)
      | ~ v1_ordinal1(A_208)
      | B_210 = A_208
      | ~ r1_tarski(A_208,B_210) ) ),
    inference(resolution,[status(thm)],[c_1281,c_634])).

tff(c_3675,plain,(
    ! [A_208] :
      ( m1_subset_1(A_208,'#skF_3')
      | ~ v3_ordinal1('#skF_4')
      | ~ v1_ordinal1(A_208)
      | A_208 = '#skF_4'
      | ~ r1_tarski(A_208,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1330,c_3631])).

tff(c_4243,plain,(
    ! [A_222] :
      ( m1_subset_1(A_222,'#skF_3')
      | ~ v1_ordinal1(A_222)
      | A_222 = '#skF_4'
      | ~ r1_tarski(A_222,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3675])).

tff(c_4258,plain,
    ( m1_subset_1('#skF_3','#skF_3')
    | ~ v1_ordinal1('#skF_3')
    | '#skF_3' = '#skF_4'
    | ~ v1_ordinal1('#skF_4')
    | v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_2992,c_4243])).

tff(c_4332,plain,
    ( m1_subset_1('#skF_3','#skF_3')
    | '#skF_3' = '#skF_4'
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_770,c_66,c_46,c_4258])).

tff(c_4333,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_626,c_1331,c_4332])).

tff(c_1902,plain,(
    ! [A_161,B_162,B_163] :
      ( m1_subset_1(A_161,B_162)
      | ~ r1_tarski(B_163,B_162)
      | v1_xboole_0(B_163)
      | ~ m1_subset_1(A_161,B_163) ) ),
    inference(resolution,[status(thm)],[c_24,c_752])).

tff(c_1920,plain,(
    ! [A_161] :
      ( m1_subset_1(A_161,'#skF_3')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_161,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1330,c_1902])).

tff(c_1986,plain,(
    ! [A_165] :
      ( m1_subset_1(A_165,'#skF_3')
      | ~ m1_subset_1(A_165,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_626,c_1920])).

tff(c_2002,plain,(
    ~ m1_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_1986,c_1331])).

tff(c_4393,plain,(
    ~ m1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4333,c_2002])).

tff(c_4429,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_770,c_4393])).

tff(c_4430,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_4467,plain,(
    ! [C_228,B_229,A_230] :
      ( ~ v1_xboole_0(C_228)
      | ~ m1_subset_1(B_229,k1_zfmisc_1(C_228))
      | ~ r2_hidden(A_230,B_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4525,plain,(
    ! [B_240,A_241,A_242] :
      ( ~ v1_xboole_0(B_240)
      | ~ r2_hidden(A_241,A_242)
      | ~ r1_tarski(A_242,B_240) ) ),
    inference(resolution,[status(thm)],[c_28,c_4467])).

tff(c_4535,plain,(
    ! [B_243] :
      ( ~ v1_xboole_0(B_243)
      | ~ r1_tarski('#skF_5',B_243) ) ),
    inference(resolution,[status(thm)],[c_38,c_4525])).

tff(c_4539,plain,
    ( ~ v1_xboole_0('#skF_5')
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_4482,c_4535])).

tff(c_4542,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4430,c_4539])).

tff(c_4887,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4874,c_4542])).

tff(c_4901,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4887])).

%------------------------------------------------------------------------------

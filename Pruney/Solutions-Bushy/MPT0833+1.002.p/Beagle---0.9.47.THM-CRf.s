%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0833+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:55 EST 2020

% Result     : Theorem 4.57s
% Output     : CNFRefutation 4.64s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 248 expanded)
%              Number of leaves         :   32 (  96 expanded)
%              Depth                    :   13
%              Number of atoms          :  208 ( 588 expanded)
%              Number of equality atoms :   36 (  60 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(B,C)
         => r2_relset_1(A,B,k6_relset_1(A,B,C,D),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( C = k8_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(E,A)
                  & r2_hidden(k4_tarski(D,E),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1890,plain,(
    ! [A_397,B_398,D_399] :
      ( r2_relset_1(A_397,B_398,D_399,D_399)
      | ~ m1_subset_1(D_399,k1_zfmisc_1(k2_zfmisc_1(A_397,B_398))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1897,plain,(
    r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_1890])).

tff(c_60,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_69,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_60])).

tff(c_2225,plain,(
    ! [A_517,B_518,C_519] :
      ( r2_hidden(k4_tarski('#skF_1'(A_517,B_518,C_519),'#skF_2'(A_517,B_518,C_519)),B_518)
      | r2_hidden(k4_tarski('#skF_3'(A_517,B_518,C_519),'#skF_4'(A_517,B_518,C_519)),C_519)
      | k8_relat_1(A_517,B_518) = C_519
      | ~ v1_relat_1(C_519)
      | ~ v1_relat_1(B_518) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10,plain,(
    ! [A_4,B_5,C_15] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_4,B_5,C_15),'#skF_2'(A_4,B_5,C_15)),C_15)
      | r2_hidden(k4_tarski('#skF_3'(A_4,B_5,C_15),'#skF_4'(A_4,B_5,C_15)),C_15)
      | k8_relat_1(A_4,B_5) = C_15
      | ~ v1_relat_1(C_15)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2308,plain,(
    ! [A_520,B_521] :
      ( r2_hidden(k4_tarski('#skF_3'(A_520,B_521,B_521),'#skF_4'(A_520,B_521,B_521)),B_521)
      | k8_relat_1(A_520,B_521) = B_521
      | ~ v1_relat_1(B_521) ) ),
    inference(resolution,[status(thm)],[c_2225,c_10])).

tff(c_110,plain,(
    ! [A_77,B_78,D_79] :
      ( r2_relset_1(A_77,B_78,D_79,D_79)
      | ~ m1_subset_1(D_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_117,plain,(
    r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_110])).

tff(c_46,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_34,plain,(
    ! [A_34,B_35] :
      ( r2_hidden(A_34,B_35)
      | v1_xboole_0(B_35)
      | ~ m1_subset_1(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_38,plain,(
    ! [A_36,B_37] :
      ( m1_subset_1(A_36,k1_zfmisc_1(B_37))
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_76,plain,(
    ! [C_56,B_57,A_58] :
      ( ~ v1_xboole_0(C_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(C_56))
      | ~ r2_hidden(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_84,plain,(
    ! [B_59,A_60,A_61] :
      ( ~ v1_xboole_0(B_59)
      | ~ r2_hidden(A_60,A_61)
      | ~ r1_tarski(A_61,B_59) ) ),
    inference(resolution,[status(thm)],[c_38,c_76])).

tff(c_123,plain,(
    ! [B_83,B_84,A_85] :
      ( ~ v1_xboole_0(B_83)
      | ~ r1_tarski(B_84,B_83)
      | v1_xboole_0(B_84)
      | ~ m1_subset_1(A_85,B_84) ) ),
    inference(resolution,[status(thm)],[c_34,c_84])).

tff(c_129,plain,(
    ! [A_85] :
      ( ~ v1_xboole_0('#skF_7')
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_85,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_46,c_123])).

tff(c_130,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_12,plain,(
    ! [A_4,B_5,C_15] :
      ( r2_hidden(k4_tarski('#skF_1'(A_4,B_5,C_15),'#skF_2'(A_4,B_5,C_15)),B_5)
      | r2_hidden(k4_tarski('#skF_3'(A_4,B_5,C_15),'#skF_4'(A_4,B_5,C_15)),C_15)
      | k8_relat_1(A_4,B_5) = C_15
      | ~ v1_relat_1(C_15)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_536,plain,(
    ! [A_191,B_192,C_193] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_191,B_192,C_193),'#skF_2'(A_191,B_192,C_193)),C_193)
      | r2_hidden(k4_tarski('#skF_3'(A_191,B_192,C_193),'#skF_4'(A_191,B_192,C_193)),C_193)
      | k8_relat_1(A_191,B_192) = C_193
      | ~ v1_relat_1(C_193)
      | ~ v1_relat_1(B_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_558,plain,(
    ! [A_195,B_196] :
      ( r2_hidden(k4_tarski('#skF_3'(A_195,B_196,B_196),'#skF_4'(A_195,B_196,B_196)),B_196)
      | k8_relat_1(A_195,B_196) = B_196
      | ~ v1_relat_1(B_196) ) ),
    inference(resolution,[status(thm)],[c_12,c_536])).

tff(c_82,plain,(
    ! [A_58] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(A_58,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_48,c_76])).

tff(c_83,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_98,plain,(
    ! [A_70,C_71,B_72] :
      ( m1_subset_1(A_70,C_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(C_71))
      | ~ r2_hidden(A_70,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_104,plain,(
    ! [A_70] :
      ( m1_subset_1(A_70,k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(A_70,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_48,c_98])).

tff(c_88,plain,(
    ! [B_62,D_63,A_64,C_65] :
      ( r2_hidden(B_62,D_63)
      | ~ r2_hidden(k4_tarski(A_64,B_62),k2_zfmisc_1(C_65,D_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_184,plain,(
    ! [B_111,D_112,C_113,A_114] :
      ( r2_hidden(B_111,D_112)
      | v1_xboole_0(k2_zfmisc_1(C_113,D_112))
      | ~ m1_subset_1(k4_tarski(A_114,B_111),k2_zfmisc_1(C_113,D_112)) ) ),
    inference(resolution,[status(thm)],[c_34,c_88])).

tff(c_188,plain,(
    ! [B_111,A_114] :
      ( r2_hidden(B_111,'#skF_6')
      | v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(k4_tarski(A_114,B_111),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_104,c_184])).

tff(c_191,plain,(
    ! [B_111,A_114] :
      ( r2_hidden(B_111,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_114,B_111),'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_188])).

tff(c_570,plain,(
    ! [A_195] :
      ( r2_hidden('#skF_4'(A_195,'#skF_8','#skF_8'),'#skF_6')
      | k8_relat_1(A_195,'#skF_8') = '#skF_8'
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_558,c_191])).

tff(c_606,plain,(
    ! [A_198] :
      ( r2_hidden('#skF_4'(A_198,'#skF_8','#skF_8'),'#skF_6')
      | k8_relat_1(A_198,'#skF_8') = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_570])).

tff(c_103,plain,(
    ! [A_70,B_37,A_36] :
      ( m1_subset_1(A_70,B_37)
      | ~ r2_hidden(A_70,A_36)
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(resolution,[status(thm)],[c_38,c_98])).

tff(c_611,plain,(
    ! [A_198,B_37] :
      ( m1_subset_1('#skF_4'(A_198,'#skF_8','#skF_8'),B_37)
      | ~ r1_tarski('#skF_6',B_37)
      | k8_relat_1(A_198,'#skF_8') = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_606,c_103])).

tff(c_553,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(k4_tarski('#skF_3'(A_4,B_5,B_5),'#skF_4'(A_4,B_5,B_5)),B_5)
      | k8_relat_1(A_4,B_5) = B_5
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_536])).

tff(c_1000,plain,(
    ! [A_235,B_236,C_237] :
      ( r2_hidden(k4_tarski('#skF_1'(A_235,B_236,C_237),'#skF_2'(A_235,B_236,C_237)),B_236)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_235,B_236,C_237),'#skF_4'(A_235,B_236,C_237)),B_236)
      | ~ r2_hidden('#skF_4'(A_235,B_236,C_237),A_235)
      | k8_relat_1(A_235,B_236) = C_237
      | ~ v1_relat_1(C_237)
      | ~ v1_relat_1(B_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_4,B_5,C_15] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_4,B_5,C_15),'#skF_2'(A_4,B_5,C_15)),C_15)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_4,B_5,C_15),'#skF_4'(A_4,B_5,C_15)),B_5)
      | ~ r2_hidden('#skF_4'(A_4,B_5,C_15),A_4)
      | k8_relat_1(A_4,B_5) = C_15
      | ~ v1_relat_1(C_15)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1175,plain,(
    ! [A_247,B_248] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_247,B_248,B_248),'#skF_4'(A_247,B_248,B_248)),B_248)
      | ~ r2_hidden('#skF_4'(A_247,B_248,B_248),A_247)
      | k8_relat_1(A_247,B_248) = B_248
      | ~ v1_relat_1(B_248) ) ),
    inference(resolution,[status(thm)],[c_1000,c_4])).

tff(c_1216,plain,(
    ! [A_249,B_250] :
      ( ~ r2_hidden('#skF_4'(A_249,B_250,B_250),A_249)
      | k8_relat_1(A_249,B_250) = B_250
      | ~ v1_relat_1(B_250) ) ),
    inference(resolution,[status(thm)],[c_553,c_1175])).

tff(c_1236,plain,(
    ! [B_251,B_252] :
      ( k8_relat_1(B_251,B_252) = B_252
      | ~ v1_relat_1(B_252)
      | v1_xboole_0(B_251)
      | ~ m1_subset_1('#skF_4'(B_251,B_252,B_252),B_251) ) ),
    inference(resolution,[status(thm)],[c_34,c_1216])).

tff(c_1240,plain,(
    ! [B_37] :
      ( ~ v1_relat_1('#skF_8')
      | v1_xboole_0(B_37)
      | ~ r1_tarski('#skF_6',B_37)
      | k8_relat_1(B_37,'#skF_8') = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_611,c_1236])).

tff(c_1256,plain,(
    ! [B_253] :
      ( v1_xboole_0(B_253)
      | ~ r1_tarski('#skF_6',B_253)
      | k8_relat_1(B_253,'#skF_8') = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_1240])).

tff(c_1259,plain,
    ( v1_xboole_0('#skF_7')
    | k8_relat_1('#skF_7','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_46,c_1256])).

tff(c_1262,plain,(
    k8_relat_1('#skF_7','#skF_8') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_1259])).

tff(c_156,plain,(
    ! [A_98,B_99,C_100,D_101] :
      ( k6_relset_1(A_98,B_99,C_100,D_101) = k8_relat_1(C_100,D_101)
      | ~ m1_subset_1(D_101,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_163,plain,(
    ! [C_100] : k6_relset_1('#skF_5','#skF_6',C_100,'#skF_8') = k8_relat_1(C_100,'#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_156])).

tff(c_44,plain,(
    ~ r2_relset_1('#skF_5','#skF_6',k6_relset_1('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_164,plain,(
    ~ r2_relset_1('#skF_5','#skF_6',k8_relat_1('#skF_7','#skF_8'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_44])).

tff(c_1263,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1262,c_164])).

tff(c_1266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_1263])).

tff(c_1268,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_1555,plain,(
    ! [A_352,B_353,C_354] :
      ( r2_hidden(k4_tarski('#skF_1'(A_352,B_353,C_354),'#skF_2'(A_352,B_353,C_354)),B_353)
      | r2_hidden(k4_tarski('#skF_3'(A_352,B_353,C_354),'#skF_4'(A_352,B_353,C_354)),C_354)
      | k8_relat_1(A_352,B_353) = C_354
      | ~ v1_relat_1(C_354)
      | ~ v1_relat_1(B_353) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1745,plain,(
    ! [A_367,B_368] :
      ( r2_hidden(k4_tarski('#skF_3'(A_367,B_368,B_368),'#skF_4'(A_367,B_368,B_368)),B_368)
      | k8_relat_1(A_367,B_368) = B_368
      | ~ v1_relat_1(B_368) ) ),
    inference(resolution,[status(thm)],[c_1555,c_10])).

tff(c_1318,plain,(
    ! [B_276,D_277,C_278,A_279] :
      ( r2_hidden(B_276,D_277)
      | v1_xboole_0(k2_zfmisc_1(C_278,D_277))
      | ~ m1_subset_1(k4_tarski(A_279,B_276),k2_zfmisc_1(C_278,D_277)) ) ),
    inference(resolution,[status(thm)],[c_34,c_88])).

tff(c_1322,plain,(
    ! [B_276,A_279] :
      ( r2_hidden(B_276,'#skF_6')
      | v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(k4_tarski(A_279,B_276),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_104,c_1318])).

tff(c_1325,plain,(
    ! [B_276,A_279] :
      ( r2_hidden(B_276,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_279,B_276),'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_1322])).

tff(c_1761,plain,(
    ! [A_367] :
      ( r2_hidden('#skF_4'(A_367,'#skF_8','#skF_8'),'#skF_6')
      | k8_relat_1(A_367,'#skF_8') = '#skF_8'
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1745,c_1325])).

tff(c_1820,plain,(
    ! [A_373] :
      ( r2_hidden('#skF_4'(A_373,'#skF_8','#skF_8'),'#skF_6')
      | k8_relat_1(A_373,'#skF_8') = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_1761])).

tff(c_81,plain,(
    ! [B_37,A_58,A_36] :
      ( ~ v1_xboole_0(B_37)
      | ~ r2_hidden(A_58,A_36)
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(resolution,[status(thm)],[c_38,c_76])).

tff(c_1826,plain,(
    ! [B_37,A_373] :
      ( ~ v1_xboole_0(B_37)
      | ~ r1_tarski('#skF_6',B_37)
      | k8_relat_1(A_373,'#skF_8') = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_1820,c_81])).

tff(c_1828,plain,(
    ! [B_374] :
      ( ~ v1_xboole_0(B_374)
      | ~ r1_tarski('#skF_6',B_374) ) ),
    inference(splitLeft,[status(thm)],[c_1826])).

tff(c_1831,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_1828])).

tff(c_1835,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1268,c_1831])).

tff(c_1836,plain,(
    ! [A_373] : k8_relat_1(A_373,'#skF_8') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1826])).

tff(c_1295,plain,(
    ! [A_267,B_268,C_269,D_270] :
      ( k6_relset_1(A_267,B_268,C_269,D_270) = k8_relat_1(C_269,D_270)
      | ~ m1_subset_1(D_270,k1_zfmisc_1(k2_zfmisc_1(A_267,B_268))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1302,plain,(
    ! [C_269] : k6_relset_1('#skF_5','#skF_6',C_269,'#skF_8') = k8_relat_1(C_269,'#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_1295])).

tff(c_1303,plain,(
    ~ r2_relset_1('#skF_5','#skF_6',k8_relat_1('#skF_7','#skF_8'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1302,c_44])).

tff(c_1840,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1836,c_1303])).

tff(c_1844,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_1840])).

tff(c_1845,plain,(
    ! [A_58] : ~ r2_hidden(A_58,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_2338,plain,(
    ! [A_520] :
      ( k8_relat_1(A_520,'#skF_8') = '#skF_8'
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2308,c_1845])).

tff(c_2349,plain,(
    ! [A_520] : k8_relat_1(A_520,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_2338])).

tff(c_1927,plain,(
    ! [A_415,B_416,C_417,D_418] :
      ( k6_relset_1(A_415,B_416,C_417,D_418) = k8_relat_1(C_417,D_418)
      | ~ m1_subset_1(D_418,k1_zfmisc_1(k2_zfmisc_1(A_415,B_416))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1934,plain,(
    ! [C_417] : k6_relset_1('#skF_5','#skF_6',C_417,'#skF_8') = k8_relat_1(C_417,'#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_1927])).

tff(c_1935,plain,(
    ~ r2_relset_1('#skF_5','#skF_6',k8_relat_1('#skF_7','#skF_8'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1934,c_44])).

tff(c_2351,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2349,c_1935])).

tff(c_2355,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1897,c_2351])).

%------------------------------------------------------------------------------

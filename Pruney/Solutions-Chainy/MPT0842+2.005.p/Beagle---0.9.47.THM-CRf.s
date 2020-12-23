%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:36 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 273 expanded)
%              Number of leaves         :   31 ( 104 expanded)
%              Depth                    :    9
%              Number of atoms          :  229 ( 823 expanded)
%              Number of equality atoms :    9 (  24 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ~ v1_xboole_0(C)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
                   => ! [E] :
                        ( m1_subset_1(E,A)
                       => ( r2_hidden(E,k8_relset_1(A,C,D,B))
                        <=> ? [F] :
                              ( m1_subset_1(F,C)
                              & r2_hidden(k4_tarski(E,F),D)
                              & r2_hidden(F,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( r2_hidden(C,k2_relat_1(B))
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_57,plain,(
    ! [C_120,B_121,A_122] :
      ( v5_relat_1(C_120,B_121)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_122,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_61,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_57])).

tff(c_52,plain,(
    ! [C_117,A_118,B_119] :
      ( v1_relat_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_56,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_52])).

tff(c_772,plain,(
    ! [A_286,B_287,C_288,D_289] :
      ( k8_relset_1(A_286,B_287,C_288,D_289) = k10_relat_1(C_288,D_289)
      | ~ m1_subset_1(C_288,k1_zfmisc_1(k2_zfmisc_1(A_286,B_287))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_775,plain,(
    ! [D_289] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_289) = k10_relat_1('#skF_5',D_289) ),
    inference(resolution,[status(thm)],[c_28,c_772])).

tff(c_551,plain,(
    ! [A_235,B_236,C_237,D_238] :
      ( k8_relset_1(A_235,B_236,C_237,D_238) = k10_relat_1(C_237,D_238)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_235,B_236))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_554,plain,(
    ! [D_238] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_238) = k10_relat_1('#skF_5',D_238) ),
    inference(resolution,[status(thm)],[c_28,c_551])).

tff(c_344,plain,(
    ! [A_189,B_190,C_191,D_192] :
      ( k8_relset_1(A_189,B_190,C_191,D_192) = k10_relat_1(C_191,D_192)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_347,plain,(
    ! [D_192] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_192) = k10_relat_1('#skF_5',D_192) ),
    inference(resolution,[status(thm)],[c_28,c_344])).

tff(c_50,plain,
    ( r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3'))
    | m1_subset_1('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_72,plain,(
    m1_subset_1('#skF_7','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_42,plain,
    ( r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3'))
    | r2_hidden('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_62,plain,(
    r2_hidden('#skF_7','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_46,plain,
    ( r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3'))
    | r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_75,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_132,plain,(
    ! [A_142,B_143,C_144,D_145] :
      ( k8_relset_1(A_142,B_143,C_144,D_145) = k10_relat_1(C_144,D_145)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_135,plain,(
    ! [D_145] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_145) = k10_relat_1('#skF_5',D_145) ),
    inference(resolution,[status(thm)],[c_28,c_132])).

tff(c_36,plain,(
    ! [F_114] :
      ( ~ r2_hidden(F_114,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_114),'#skF_5')
      | ~ m1_subset_1(F_114,'#skF_4')
      | ~ r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_238,plain,(
    ! [F_114] :
      ( ~ r2_hidden(F_114,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_114),'#skF_5')
      | ~ m1_subset_1(F_114,'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_36])).

tff(c_239,plain,(
    ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_238])).

tff(c_14,plain,(
    ! [B_14,C_15,A_13] :
      ( r2_hidden(B_14,k2_relat_1(C_15))
      | ~ r2_hidden(k4_tarski(A_13,B_14),C_15)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_78,plain,
    ( r2_hidden('#skF_7',k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_75,c_14])).

tff(c_87,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_78])).

tff(c_240,plain,(
    ! [A_170,C_171,B_172,D_173] :
      ( r2_hidden(A_170,k10_relat_1(C_171,B_172))
      | ~ r2_hidden(D_173,B_172)
      | ~ r2_hidden(k4_tarski(A_170,D_173),C_171)
      | ~ r2_hidden(D_173,k2_relat_1(C_171))
      | ~ v1_relat_1(C_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_268,plain,(
    ! [A_174,C_175] :
      ( r2_hidden(A_174,k10_relat_1(C_175,'#skF_3'))
      | ~ r2_hidden(k4_tarski(A_174,'#skF_7'),C_175)
      | ~ r2_hidden('#skF_7',k2_relat_1(C_175))
      | ~ v1_relat_1(C_175) ) ),
    inference(resolution,[status(thm)],[c_62,c_240])).

tff(c_271,plain,
    ( r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ r2_hidden('#skF_7',k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_75,c_268])).

tff(c_274,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_87,c_271])).

tff(c_276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_239,c_274])).

tff(c_299,plain,(
    ! [F_176] :
      ( ~ r2_hidden(F_176,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_176),'#skF_5')
      | ~ m1_subset_1(F_176,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_238])).

tff(c_306,plain,
    ( ~ r2_hidden('#skF_7','#skF_3')
    | ~ m1_subset_1('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_75,c_299])).

tff(c_313,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_62,c_306])).

tff(c_314,plain,(
    r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_350,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_314])).

tff(c_330,plain,(
    ! [A_183,B_184,C_185] :
      ( r2_hidden('#skF_1'(A_183,B_184,C_185),k2_relat_1(C_185))
      | ~ r2_hidden(A_183,k10_relat_1(C_185,B_184))
      | ~ v1_relat_1(C_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_12,plain,(
    ! [C_12,A_9,B_10] :
      ( r2_hidden(C_12,A_9)
      | ~ r2_hidden(C_12,k2_relat_1(B_10))
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_442,plain,(
    ! [A_207,B_208,C_209,A_210] :
      ( r2_hidden('#skF_1'(A_207,B_208,C_209),A_210)
      | ~ v5_relat_1(C_209,A_210)
      | ~ r2_hidden(A_207,k10_relat_1(C_209,B_208))
      | ~ v1_relat_1(C_209) ) ),
    inference(resolution,[status(thm)],[c_330,c_12])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_460,plain,(
    ! [A_211,B_212,C_213,A_214] :
      ( m1_subset_1('#skF_1'(A_211,B_212,C_213),A_214)
      | ~ v5_relat_1(C_213,A_214)
      | ~ r2_hidden(A_211,k10_relat_1(C_213,B_212))
      | ~ v1_relat_1(C_213) ) ),
    inference(resolution,[status(thm)],[c_442,c_2])).

tff(c_468,plain,(
    ! [A_214] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_214)
      | ~ v5_relat_1('#skF_5',A_214)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_350,c_460])).

tff(c_476,plain,(
    ! [A_214] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_214)
      | ~ v5_relat_1('#skF_5',A_214) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_468])).

tff(c_6,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),B_4)
      | ~ r2_hidden(A_3,k10_relat_1(C_5,B_4))
      | ~ v1_relat_1(C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden(k4_tarski(A_3,'#skF_1'(A_3,B_4,C_5)),C_5)
      | ~ r2_hidden(A_3,k10_relat_1(C_5,B_4))
      | ~ v1_relat_1(C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_315,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_44,plain,(
    ! [F_114] :
      ( ~ r2_hidden(F_114,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_114),'#skF_5')
      | ~ m1_subset_1(F_114,'#skF_4')
      | r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_414,plain,(
    ! [F_203] :
      ( ~ r2_hidden(F_203,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_203),'#skF_5')
      | ~ m1_subset_1(F_203,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_44])).

tff(c_418,plain,(
    ! [B_4] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_4,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_4,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_4))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8,c_414])).

tff(c_502,plain,(
    ! [B_218] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_218,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_218,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_218)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_418])).

tff(c_510,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_502])).

tff(c_516,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_350,c_510])).

tff(c_519,plain,(
    ~ v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_476,c_516])).

tff(c_523,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_519])).

tff(c_524,plain,(
    r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_556,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_554,c_524])).

tff(c_566,plain,(
    ! [A_240,B_241,C_242] :
      ( r2_hidden('#skF_1'(A_240,B_241,C_242),k2_relat_1(C_242))
      | ~ r2_hidden(A_240,k10_relat_1(C_242,B_241))
      | ~ v1_relat_1(C_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_656,plain,(
    ! [A_255,B_256,C_257,A_258] :
      ( r2_hidden('#skF_1'(A_255,B_256,C_257),A_258)
      | ~ v5_relat_1(C_257,A_258)
      | ~ r2_hidden(A_255,k10_relat_1(C_257,B_256))
      | ~ v1_relat_1(C_257) ) ),
    inference(resolution,[status(thm)],[c_566,c_12])).

tff(c_674,plain,(
    ! [A_259,B_260,C_261,A_262] :
      ( m1_subset_1('#skF_1'(A_259,B_260,C_261),A_262)
      | ~ v5_relat_1(C_261,A_262)
      | ~ r2_hidden(A_259,k10_relat_1(C_261,B_260))
      | ~ v1_relat_1(C_261) ) ),
    inference(resolution,[status(thm)],[c_656,c_2])).

tff(c_682,plain,(
    ! [A_262] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_262)
      | ~ v5_relat_1('#skF_5',A_262)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_556,c_674])).

tff(c_690,plain,(
    ! [A_262] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_262)
      | ~ v5_relat_1('#skF_5',A_262) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_682])).

tff(c_585,plain,(
    ! [A_246,B_247,C_248] :
      ( r2_hidden(k4_tarski(A_246,'#skF_1'(A_246,B_247,C_248)),C_248)
      | ~ r2_hidden(A_246,k10_relat_1(C_248,B_247))
      | ~ v1_relat_1(C_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_525,plain,(
    ~ m1_subset_1('#skF_7','#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,(
    ! [F_114] :
      ( ~ r2_hidden(F_114,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_114),'#skF_5')
      | ~ m1_subset_1(F_114,'#skF_4')
      | m1_subset_1('#skF_7','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_549,plain,(
    ! [F_114] :
      ( ~ r2_hidden(F_114,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_114),'#skF_5')
      | ~ m1_subset_1(F_114,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_525,c_48])).

tff(c_589,plain,(
    ! [B_247] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_247,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_247,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_247))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_585,c_549])).

tff(c_712,plain,(
    ! [B_264] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_264,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_264,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_264)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_589])).

tff(c_720,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_712])).

tff(c_726,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_556,c_720])).

tff(c_729,plain,(
    ~ v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_690,c_726])).

tff(c_733,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_729])).

tff(c_734,plain,(
    r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_777,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_775,c_734])).

tff(c_764,plain,(
    ! [A_283,B_284,C_285] :
      ( r2_hidden('#skF_1'(A_283,B_284,C_285),k2_relat_1(C_285))
      | ~ r2_hidden(A_283,k10_relat_1(C_285,B_284))
      | ~ v1_relat_1(C_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1044,plain,(
    ! [A_333,B_334,C_335,A_336] :
      ( r2_hidden('#skF_1'(A_333,B_334,C_335),A_336)
      | ~ v5_relat_1(C_335,A_336)
      | ~ r2_hidden(A_333,k10_relat_1(C_335,B_334))
      | ~ v1_relat_1(C_335) ) ),
    inference(resolution,[status(thm)],[c_764,c_12])).

tff(c_1062,plain,(
    ! [A_337,B_338,C_339,A_340] :
      ( m1_subset_1('#skF_1'(A_337,B_338,C_339),A_340)
      | ~ v5_relat_1(C_339,A_340)
      | ~ r2_hidden(A_337,k10_relat_1(C_339,B_338))
      | ~ v1_relat_1(C_339) ) ),
    inference(resolution,[status(thm)],[c_1044,c_2])).

tff(c_1070,plain,(
    ! [A_340] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_340)
      | ~ v5_relat_1('#skF_5',A_340)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_777,c_1062])).

tff(c_1078,plain,(
    ! [A_340] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_340)
      | ~ v5_relat_1('#skF_5',A_340) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1070])).

tff(c_975,plain,(
    ! [A_324,B_325,C_326] :
      ( r2_hidden(k4_tarski(A_324,'#skF_1'(A_324,B_325,C_326)),C_326)
      | ~ r2_hidden(A_324,k10_relat_1(C_326,B_325))
      | ~ v1_relat_1(C_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_735,plain,(
    ~ r2_hidden('#skF_7','#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_40,plain,(
    ! [F_114] :
      ( ~ r2_hidden(F_114,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_114),'#skF_5')
      | ~ m1_subset_1(F_114,'#skF_4')
      | r2_hidden('#skF_7','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_972,plain,(
    ! [F_114] :
      ( ~ r2_hidden(F_114,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_114),'#skF_5')
      | ~ m1_subset_1(F_114,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_735,c_40])).

tff(c_979,plain,(
    ! [B_325] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_325,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_325,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_325))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_975,c_972])).

tff(c_1104,plain,(
    ! [B_344] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_344,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_344,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_344)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_979])).

tff(c_1112,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_1104])).

tff(c_1118,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_777,c_1112])).

tff(c_1121,plain,(
    ~ v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1078,c_1118])).

tff(c_1125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_1121])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.33/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.53  
% 3.33/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.53  %$ v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 3.33/1.53  
% 3.33/1.53  %Foreground sorts:
% 3.33/1.53  
% 3.33/1.53  
% 3.33/1.53  %Background operators:
% 3.33/1.53  
% 3.33/1.53  
% 3.33/1.53  %Foreground operators:
% 3.33/1.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.33/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.33/1.53  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.33/1.53  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.33/1.53  tff('#skF_7', type, '#skF_7': $i).
% 3.33/1.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.33/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.33/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.33/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.33/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.33/1.53  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.33/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.33/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.53  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.33/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.33/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.33/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.33/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.54  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.33/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.33/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.33/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.33/1.54  
% 3.54/1.56  tff(f_98, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k8_relset_1(A, C, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(E, F), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_relset_1)).
% 3.54/1.56  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.54/1.56  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.54/1.56  tff(f_71, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.54/1.56  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 3.54/1.56  tff(f_40, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 3.54/1.56  tff(f_49, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t202_relat_1)).
% 3.54/1.56  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.54/1.56  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.54/1.56  tff(c_57, plain, (![C_120, B_121, A_122]: (v5_relat_1(C_120, B_121) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_122, B_121))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.54/1.56  tff(c_61, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_57])).
% 3.54/1.56  tff(c_52, plain, (![C_117, A_118, B_119]: (v1_relat_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.54/1.56  tff(c_56, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_52])).
% 3.54/1.56  tff(c_772, plain, (![A_286, B_287, C_288, D_289]: (k8_relset_1(A_286, B_287, C_288, D_289)=k10_relat_1(C_288, D_289) | ~m1_subset_1(C_288, k1_zfmisc_1(k2_zfmisc_1(A_286, B_287))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.54/1.56  tff(c_775, plain, (![D_289]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_289)=k10_relat_1('#skF_5', D_289))), inference(resolution, [status(thm)], [c_28, c_772])).
% 3.54/1.56  tff(c_551, plain, (![A_235, B_236, C_237, D_238]: (k8_relset_1(A_235, B_236, C_237, D_238)=k10_relat_1(C_237, D_238) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_235, B_236))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.54/1.56  tff(c_554, plain, (![D_238]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_238)=k10_relat_1('#skF_5', D_238))), inference(resolution, [status(thm)], [c_28, c_551])).
% 3.54/1.56  tff(c_344, plain, (![A_189, B_190, C_191, D_192]: (k8_relset_1(A_189, B_190, C_191, D_192)=k10_relat_1(C_191, D_192) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.54/1.56  tff(c_347, plain, (![D_192]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_192)=k10_relat_1('#skF_5', D_192))), inference(resolution, [status(thm)], [c_28, c_344])).
% 3.54/1.56  tff(c_50, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')) | m1_subset_1('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.54/1.56  tff(c_72, plain, (m1_subset_1('#skF_7', '#skF_4')), inference(splitLeft, [status(thm)], [c_50])).
% 3.54/1.56  tff(c_42, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')) | r2_hidden('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.54/1.56  tff(c_62, plain, (r2_hidden('#skF_7', '#skF_3')), inference(splitLeft, [status(thm)], [c_42])).
% 3.54/1.56  tff(c_46, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')) | r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.54/1.56  tff(c_75, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5')), inference(splitLeft, [status(thm)], [c_46])).
% 3.54/1.56  tff(c_132, plain, (![A_142, B_143, C_144, D_145]: (k8_relset_1(A_142, B_143, C_144, D_145)=k10_relat_1(C_144, D_145) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.54/1.56  tff(c_135, plain, (![D_145]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_145)=k10_relat_1('#skF_5', D_145))), inference(resolution, [status(thm)], [c_28, c_132])).
% 3.54/1.56  tff(c_36, plain, (![F_114]: (~r2_hidden(F_114, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_114), '#skF_5') | ~m1_subset_1(F_114, '#skF_4') | ~r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.54/1.56  tff(c_238, plain, (![F_114]: (~r2_hidden(F_114, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_114), '#skF_5') | ~m1_subset_1(F_114, '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_36])).
% 3.54/1.56  tff(c_239, plain, (~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(splitLeft, [status(thm)], [c_238])).
% 3.54/1.56  tff(c_14, plain, (![B_14, C_15, A_13]: (r2_hidden(B_14, k2_relat_1(C_15)) | ~r2_hidden(k4_tarski(A_13, B_14), C_15) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.54/1.56  tff(c_78, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_75, c_14])).
% 3.54/1.56  tff(c_87, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_78])).
% 3.54/1.56  tff(c_240, plain, (![A_170, C_171, B_172, D_173]: (r2_hidden(A_170, k10_relat_1(C_171, B_172)) | ~r2_hidden(D_173, B_172) | ~r2_hidden(k4_tarski(A_170, D_173), C_171) | ~r2_hidden(D_173, k2_relat_1(C_171)) | ~v1_relat_1(C_171))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.54/1.56  tff(c_268, plain, (![A_174, C_175]: (r2_hidden(A_174, k10_relat_1(C_175, '#skF_3')) | ~r2_hidden(k4_tarski(A_174, '#skF_7'), C_175) | ~r2_hidden('#skF_7', k2_relat_1(C_175)) | ~v1_relat_1(C_175))), inference(resolution, [status(thm)], [c_62, c_240])).
% 3.54/1.56  tff(c_271, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~r2_hidden('#skF_7', k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_75, c_268])).
% 3.54/1.56  tff(c_274, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_87, c_271])).
% 3.54/1.56  tff(c_276, plain, $false, inference(negUnitSimplification, [status(thm)], [c_239, c_274])).
% 3.54/1.56  tff(c_299, plain, (![F_176]: (~r2_hidden(F_176, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_176), '#skF_5') | ~m1_subset_1(F_176, '#skF_4'))), inference(splitRight, [status(thm)], [c_238])).
% 3.54/1.56  tff(c_306, plain, (~r2_hidden('#skF_7', '#skF_3') | ~m1_subset_1('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_75, c_299])).
% 3.54/1.56  tff(c_313, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_62, c_306])).
% 3.54/1.56  tff(c_314, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_46])).
% 3.54/1.56  tff(c_350, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_347, c_314])).
% 3.54/1.56  tff(c_330, plain, (![A_183, B_184, C_185]: (r2_hidden('#skF_1'(A_183, B_184, C_185), k2_relat_1(C_185)) | ~r2_hidden(A_183, k10_relat_1(C_185, B_184)) | ~v1_relat_1(C_185))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.54/1.56  tff(c_12, plain, (![C_12, A_9, B_10]: (r2_hidden(C_12, A_9) | ~r2_hidden(C_12, k2_relat_1(B_10)) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.54/1.56  tff(c_442, plain, (![A_207, B_208, C_209, A_210]: (r2_hidden('#skF_1'(A_207, B_208, C_209), A_210) | ~v5_relat_1(C_209, A_210) | ~r2_hidden(A_207, k10_relat_1(C_209, B_208)) | ~v1_relat_1(C_209))), inference(resolution, [status(thm)], [c_330, c_12])).
% 3.54/1.56  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.54/1.56  tff(c_460, plain, (![A_211, B_212, C_213, A_214]: (m1_subset_1('#skF_1'(A_211, B_212, C_213), A_214) | ~v5_relat_1(C_213, A_214) | ~r2_hidden(A_211, k10_relat_1(C_213, B_212)) | ~v1_relat_1(C_213))), inference(resolution, [status(thm)], [c_442, c_2])).
% 3.54/1.56  tff(c_468, plain, (![A_214]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_214) | ~v5_relat_1('#skF_5', A_214) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_350, c_460])).
% 3.54/1.56  tff(c_476, plain, (![A_214]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_214) | ~v5_relat_1('#skF_5', A_214))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_468])).
% 3.54/1.56  tff(c_6, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), B_4) | ~r2_hidden(A_3, k10_relat_1(C_5, B_4)) | ~v1_relat_1(C_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.54/1.56  tff(c_8, plain, (![A_3, B_4, C_5]: (r2_hidden(k4_tarski(A_3, '#skF_1'(A_3, B_4, C_5)), C_5) | ~r2_hidden(A_3, k10_relat_1(C_5, B_4)) | ~v1_relat_1(C_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.54/1.56  tff(c_315, plain, (~r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5')), inference(splitRight, [status(thm)], [c_46])).
% 3.54/1.56  tff(c_44, plain, (![F_114]: (~r2_hidden(F_114, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_114), '#skF_5') | ~m1_subset_1(F_114, '#skF_4') | r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.54/1.56  tff(c_414, plain, (![F_203]: (~r2_hidden(F_203, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_203), '#skF_5') | ~m1_subset_1(F_203, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_315, c_44])).
% 3.54/1.56  tff(c_418, plain, (![B_4]: (~r2_hidden('#skF_1'('#skF_6', B_4, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_4, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_4)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_8, c_414])).
% 3.54/1.56  tff(c_502, plain, (![B_218]: (~r2_hidden('#skF_1'('#skF_6', B_218, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_218, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_218)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_418])).
% 3.54/1.56  tff(c_510, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_6, c_502])).
% 3.54/1.56  tff(c_516, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_350, c_510])).
% 3.54/1.56  tff(c_519, plain, (~v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_476, c_516])).
% 3.54/1.56  tff(c_523, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_519])).
% 3.54/1.56  tff(c_524, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_50])).
% 3.54/1.56  tff(c_556, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_554, c_524])).
% 3.54/1.56  tff(c_566, plain, (![A_240, B_241, C_242]: (r2_hidden('#skF_1'(A_240, B_241, C_242), k2_relat_1(C_242)) | ~r2_hidden(A_240, k10_relat_1(C_242, B_241)) | ~v1_relat_1(C_242))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.54/1.56  tff(c_656, plain, (![A_255, B_256, C_257, A_258]: (r2_hidden('#skF_1'(A_255, B_256, C_257), A_258) | ~v5_relat_1(C_257, A_258) | ~r2_hidden(A_255, k10_relat_1(C_257, B_256)) | ~v1_relat_1(C_257))), inference(resolution, [status(thm)], [c_566, c_12])).
% 3.54/1.56  tff(c_674, plain, (![A_259, B_260, C_261, A_262]: (m1_subset_1('#skF_1'(A_259, B_260, C_261), A_262) | ~v5_relat_1(C_261, A_262) | ~r2_hidden(A_259, k10_relat_1(C_261, B_260)) | ~v1_relat_1(C_261))), inference(resolution, [status(thm)], [c_656, c_2])).
% 3.54/1.56  tff(c_682, plain, (![A_262]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_262) | ~v5_relat_1('#skF_5', A_262) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_556, c_674])).
% 3.54/1.56  tff(c_690, plain, (![A_262]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_262) | ~v5_relat_1('#skF_5', A_262))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_682])).
% 3.54/1.56  tff(c_585, plain, (![A_246, B_247, C_248]: (r2_hidden(k4_tarski(A_246, '#skF_1'(A_246, B_247, C_248)), C_248) | ~r2_hidden(A_246, k10_relat_1(C_248, B_247)) | ~v1_relat_1(C_248))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.54/1.56  tff(c_525, plain, (~m1_subset_1('#skF_7', '#skF_4')), inference(splitRight, [status(thm)], [c_50])).
% 3.54/1.56  tff(c_48, plain, (![F_114]: (~r2_hidden(F_114, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_114), '#skF_5') | ~m1_subset_1(F_114, '#skF_4') | m1_subset_1('#skF_7', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.54/1.56  tff(c_549, plain, (![F_114]: (~r2_hidden(F_114, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_114), '#skF_5') | ~m1_subset_1(F_114, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_525, c_48])).
% 3.54/1.56  tff(c_589, plain, (![B_247]: (~r2_hidden('#skF_1'('#skF_6', B_247, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_247, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_247)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_585, c_549])).
% 3.54/1.56  tff(c_712, plain, (![B_264]: (~r2_hidden('#skF_1'('#skF_6', B_264, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_264, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_264)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_589])).
% 3.54/1.56  tff(c_720, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_6, c_712])).
% 3.54/1.56  tff(c_726, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_556, c_720])).
% 3.54/1.56  tff(c_729, plain, (~v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_690, c_726])).
% 3.54/1.56  tff(c_733, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_729])).
% 3.54/1.56  tff(c_734, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_42])).
% 3.54/1.56  tff(c_777, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_775, c_734])).
% 3.54/1.56  tff(c_764, plain, (![A_283, B_284, C_285]: (r2_hidden('#skF_1'(A_283, B_284, C_285), k2_relat_1(C_285)) | ~r2_hidden(A_283, k10_relat_1(C_285, B_284)) | ~v1_relat_1(C_285))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.54/1.56  tff(c_1044, plain, (![A_333, B_334, C_335, A_336]: (r2_hidden('#skF_1'(A_333, B_334, C_335), A_336) | ~v5_relat_1(C_335, A_336) | ~r2_hidden(A_333, k10_relat_1(C_335, B_334)) | ~v1_relat_1(C_335))), inference(resolution, [status(thm)], [c_764, c_12])).
% 3.54/1.56  tff(c_1062, plain, (![A_337, B_338, C_339, A_340]: (m1_subset_1('#skF_1'(A_337, B_338, C_339), A_340) | ~v5_relat_1(C_339, A_340) | ~r2_hidden(A_337, k10_relat_1(C_339, B_338)) | ~v1_relat_1(C_339))), inference(resolution, [status(thm)], [c_1044, c_2])).
% 3.54/1.56  tff(c_1070, plain, (![A_340]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_340) | ~v5_relat_1('#skF_5', A_340) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_777, c_1062])).
% 3.54/1.56  tff(c_1078, plain, (![A_340]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_340) | ~v5_relat_1('#skF_5', A_340))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1070])).
% 3.54/1.56  tff(c_975, plain, (![A_324, B_325, C_326]: (r2_hidden(k4_tarski(A_324, '#skF_1'(A_324, B_325, C_326)), C_326) | ~r2_hidden(A_324, k10_relat_1(C_326, B_325)) | ~v1_relat_1(C_326))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.54/1.56  tff(c_735, plain, (~r2_hidden('#skF_7', '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 3.54/1.56  tff(c_40, plain, (![F_114]: (~r2_hidden(F_114, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_114), '#skF_5') | ~m1_subset_1(F_114, '#skF_4') | r2_hidden('#skF_7', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.54/1.56  tff(c_972, plain, (![F_114]: (~r2_hidden(F_114, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_114), '#skF_5') | ~m1_subset_1(F_114, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_735, c_40])).
% 3.54/1.56  tff(c_979, plain, (![B_325]: (~r2_hidden('#skF_1'('#skF_6', B_325, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_325, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_325)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_975, c_972])).
% 3.54/1.56  tff(c_1104, plain, (![B_344]: (~r2_hidden('#skF_1'('#skF_6', B_344, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_344, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_344)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_979])).
% 3.54/1.56  tff(c_1112, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_6, c_1104])).
% 3.54/1.56  tff(c_1118, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_777, c_1112])).
% 3.54/1.56  tff(c_1121, plain, (~v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1078, c_1118])).
% 3.54/1.56  tff(c_1125, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_1121])).
% 3.54/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.56  
% 3.54/1.56  Inference rules
% 3.54/1.56  ----------------------
% 3.54/1.56  #Ref     : 0
% 3.54/1.56  #Sup     : 210
% 3.54/1.56  #Fact    : 0
% 3.54/1.56  #Define  : 0
% 3.54/1.56  #Split   : 8
% 3.54/1.56  #Chain   : 0
% 3.54/1.56  #Close   : 0
% 3.54/1.56  
% 3.54/1.56  Ordering : KBO
% 3.54/1.56  
% 3.54/1.56  Simplification rules
% 3.54/1.56  ----------------------
% 3.54/1.56  #Subsume      : 19
% 3.54/1.56  #Demod        : 71
% 3.54/1.56  #Tautology    : 23
% 3.54/1.56  #SimpNegUnit  : 5
% 3.54/1.56  #BackRed      : 6
% 3.54/1.56  
% 3.54/1.56  #Partial instantiations: 0
% 3.54/1.56  #Strategies tried      : 1
% 3.54/1.56  
% 3.54/1.56  Timing (in seconds)
% 3.54/1.56  ----------------------
% 3.54/1.56  Preprocessing        : 0.32
% 3.54/1.56  Parsing              : 0.16
% 3.54/1.56  CNF conversion       : 0.03
% 3.54/1.57  Main loop            : 0.46
% 3.54/1.57  Inferencing          : 0.18
% 3.54/1.57  Reduction            : 0.13
% 3.54/1.57  Demodulation         : 0.09
% 3.54/1.57  BG Simplification    : 0.02
% 3.54/1.57  Subsumption          : 0.08
% 3.54/1.57  Abstraction          : 0.02
% 3.54/1.57  MUC search           : 0.00
% 3.54/1.57  Cooper               : 0.00
% 3.54/1.57  Total                : 0.83
% 3.54/1.57  Index Insertion      : 0.00
% 3.54/1.57  Index Deletion       : 0.00
% 3.54/1.57  Index Matching       : 0.00
% 3.54/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------

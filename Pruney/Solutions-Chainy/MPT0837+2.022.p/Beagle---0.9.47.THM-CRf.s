%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:08 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 331 expanded)
%              Number of leaves         :   33 ( 123 expanded)
%              Depth                    :    9
%              Number of atoms          :  218 ( 787 expanded)
%              Number of equality atoms :   28 (  64 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ! [D] :
                    ( r2_hidden(D,k2_relset_1(B,A,C))
                  <=> ? [E] :
                        ( m1_subset_1(E,B)
                        & r2_hidden(k4_tarski(E,D),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(c_30,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_8,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_52,plain,(
    ! [B_74,A_75] :
      ( v1_relat_1(B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_75))
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_55,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_52])).

tff(c_58,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_55])).

tff(c_898,plain,(
    ! [A_246,B_247,C_248,D_249] :
      ( k7_relset_1(A_246,B_247,C_248,D_249) = k9_relat_1(C_248,D_249)
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(A_246,B_247))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_901,plain,(
    ! [D_249] : k7_relset_1('#skF_3','#skF_2','#skF_4',D_249) = k9_relat_1('#skF_4',D_249) ),
    inference(resolution,[status(thm)],[c_28,c_898])).

tff(c_932,plain,(
    ! [A_263,B_264,C_265] :
      ( k7_relset_1(A_263,B_264,C_265,A_263) = k2_relset_1(A_263,B_264,C_265)
      | ~ m1_subset_1(C_265,k1_zfmisc_1(k2_zfmisc_1(A_263,B_264))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_934,plain,(
    k7_relset_1('#skF_3','#skF_2','#skF_4','#skF_3') = k2_relset_1('#skF_3','#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_932])).

tff(c_936,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k9_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_901,c_934])).

tff(c_44,plain,
    ( m1_subset_1('#skF_6','#skF_3')
    | r2_hidden('#skF_7',k2_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_59,plain,(
    r2_hidden('#skF_7',k2_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_940,plain,(
    r2_hidden('#skF_7',k9_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_936,c_59])).

tff(c_230,plain,(
    ! [A_126,B_127,C_128] :
      ( r2_hidden('#skF_1'(A_126,B_127,C_128),B_127)
      | ~ r2_hidden(A_126,k9_relat_1(C_128,B_127))
      | ~ v1_relat_1(C_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_234,plain,(
    ! [A_126,B_127,C_128] :
      ( m1_subset_1('#skF_1'(A_126,B_127,C_128),B_127)
      | ~ r2_hidden(A_126,k9_relat_1(C_128,B_127))
      | ~ v1_relat_1(C_128) ) ),
    inference(resolution,[status(thm)],[c_230,c_2])).

tff(c_946,plain,
    ( m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_940,c_234])).

tff(c_952,plain,(
    m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_946])).

tff(c_965,plain,(
    ! [A_266,B_267,C_268] :
      ( r2_hidden(k4_tarski('#skF_1'(A_266,B_267,C_268),A_266),C_268)
      | ~ r2_hidden(A_266,k9_relat_1(C_268,B_267))
      | ~ v1_relat_1(C_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_107,plain,(
    ! [A_99,B_100,C_101,D_102] :
      ( k7_relset_1(A_99,B_100,C_101,D_102) = k9_relat_1(C_101,D_102)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_110,plain,(
    ! [D_102] : k7_relset_1('#skF_3','#skF_2','#skF_4',D_102) = k9_relat_1('#skF_4',D_102) ),
    inference(resolution,[status(thm)],[c_28,c_107])).

tff(c_121,plain,(
    ! [A_107,B_108,C_109] :
      ( k7_relset_1(A_107,B_108,C_109,A_107) = k2_relset_1(A_107,B_108,C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_123,plain,(
    k7_relset_1('#skF_3','#skF_2','#skF_4','#skF_3') = k2_relset_1('#skF_3','#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_121])).

tff(c_125,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k9_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_123])).

tff(c_127,plain,(
    r2_hidden('#skF_7',k9_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_59])).

tff(c_86,plain,(
    ! [A_84,B_85,C_86] :
      ( r2_hidden('#skF_1'(A_84,B_85,C_86),B_85)
      | ~ r2_hidden(A_84,k9_relat_1(C_86,B_85))
      | ~ v1_relat_1(C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_90,plain,(
    ! [A_84,B_85,C_86] :
      ( m1_subset_1('#skF_1'(A_84,B_85,C_86),B_85)
      | ~ r2_hidden(A_84,k9_relat_1(C_86,B_85))
      | ~ v1_relat_1(C_86) ) ),
    inference(resolution,[status(thm)],[c_86,c_2])).

tff(c_133,plain,
    ( m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_127,c_90])).

tff(c_139,plain,(
    m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_133])).

tff(c_142,plain,(
    ! [A_110,B_111,C_112] :
      ( r2_hidden(k4_tarski('#skF_1'(A_110,B_111,C_112),A_110),C_112)
      | ~ r2_hidden(A_110,k9_relat_1(C_112,B_111))
      | ~ v1_relat_1(C_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_38,plain,(
    ! [E_67] :
      ( m1_subset_1('#skF_6','#skF_3')
      | ~ r2_hidden(k4_tarski(E_67,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(E_67,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_60,plain,(
    ! [E_67] :
      ( ~ r2_hidden(k4_tarski(E_67,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(E_67,'#skF_3') ) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_155,plain,(
    ! [B_111] :
      ( ~ m1_subset_1('#skF_1'('#skF_7',B_111,'#skF_4'),'#skF_3')
      | ~ r2_hidden('#skF_7',k9_relat_1('#skF_4',B_111))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_142,c_60])).

tff(c_200,plain,(
    ! [B_119] :
      ( ~ m1_subset_1('#skF_1'('#skF_7',B_119,'#skF_4'),'#skF_3')
      | ~ r2_hidden('#skF_7',k9_relat_1('#skF_4',B_119)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_155])).

tff(c_203,plain,(
    ~ m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_127,c_200])).

tff(c_210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_203])).

tff(c_211,plain,(
    m1_subset_1('#skF_6','#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_256,plain,(
    ! [A_140,B_141,C_142,D_143] :
      ( k7_relset_1(A_140,B_141,C_142,D_143) = k9_relat_1(C_142,D_143)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_259,plain,(
    ! [D_143] : k7_relset_1('#skF_3','#skF_2','#skF_4',D_143) = k9_relat_1('#skF_4',D_143) ),
    inference(resolution,[status(thm)],[c_28,c_256])).

tff(c_332,plain,(
    ! [A_161,B_162,C_163] :
      ( k7_relset_1(A_161,B_162,C_163,A_161) = k2_relset_1(A_161,B_162,C_163)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_334,plain,(
    k7_relset_1('#skF_3','#skF_2','#skF_4','#skF_3') = k2_relset_1('#skF_3','#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_332])).

tff(c_336,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k9_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_334])).

tff(c_340,plain,(
    r2_hidden('#skF_7',k9_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_59])).

tff(c_356,plain,
    ( m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_340,c_234])).

tff(c_366,plain,(
    m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_356])).

tff(c_287,plain,(
    ! [A_154,B_155,C_156] :
      ( r2_hidden(k4_tarski('#skF_1'(A_154,B_155,C_156),A_154),C_156)
      | ~ r2_hidden(A_154,k9_relat_1(C_156,B_155))
      | ~ v1_relat_1(C_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_36,plain,(
    ! [E_67] :
      ( r2_hidden(k4_tarski('#skF_6','#skF_5'),'#skF_4')
      | ~ r2_hidden(k4_tarski(E_67,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(E_67,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_235,plain,(
    ! [E_67] :
      ( ~ r2_hidden(k4_tarski(E_67,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(E_67,'#skF_3') ) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_294,plain,(
    ! [B_155] :
      ( ~ m1_subset_1('#skF_1'('#skF_7',B_155,'#skF_4'),'#skF_3')
      | ~ r2_hidden('#skF_7',k9_relat_1('#skF_4',B_155))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_287,c_235])).

tff(c_307,plain,(
    ! [B_155] :
      ( ~ m1_subset_1('#skF_1'('#skF_7',B_155,'#skF_4'),'#skF_3')
      | ~ r2_hidden('#skF_7',k9_relat_1('#skF_4',B_155)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_294])).

tff(c_360,plain,(
    ~ m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_340,c_307])).

tff(c_393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_360])).

tff(c_394,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_20,plain,(
    ! [A_16,C_18,B_17] :
      ( r2_hidden(A_16,k1_relat_1(C_18))
      | ~ r2_hidden(k4_tarski(A_16,B_17),C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_398,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_394,c_20])).

tff(c_407,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_398])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_599,plain,(
    ! [A_209,C_210,B_211,D_212] :
      ( r2_hidden(A_209,k9_relat_1(C_210,B_211))
      | ~ r2_hidden(D_212,B_211)
      | ~ r2_hidden(k4_tarski(D_212,A_209),C_210)
      | ~ r2_hidden(D_212,k1_relat_1(C_210))
      | ~ v1_relat_1(C_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_803,plain,(
    ! [A_236,C_237,B_238,A_239] :
      ( r2_hidden(A_236,k9_relat_1(C_237,B_238))
      | ~ r2_hidden(k4_tarski(A_239,A_236),C_237)
      | ~ r2_hidden(A_239,k1_relat_1(C_237))
      | ~ v1_relat_1(C_237)
      | v1_xboole_0(B_238)
      | ~ m1_subset_1(A_239,B_238) ) ),
    inference(resolution,[status(thm)],[c_4,c_599])).

tff(c_819,plain,(
    ! [B_238] :
      ( r2_hidden('#skF_5',k9_relat_1('#skF_4',B_238))
      | ~ r2_hidden('#skF_6',k1_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4')
      | v1_xboole_0(B_238)
      | ~ m1_subset_1('#skF_6',B_238) ) ),
    inference(resolution,[status(thm)],[c_394,c_803])).

tff(c_832,plain,(
    ! [B_240] :
      ( r2_hidden('#skF_5',k9_relat_1('#skF_4',B_240))
      | v1_xboole_0(B_240)
      | ~ m1_subset_1('#skF_6',B_240) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_407,c_819])).

tff(c_451,plain,(
    ! [A_180,B_181,C_182,D_183] :
      ( k7_relset_1(A_180,B_181,C_182,D_183) = k9_relat_1(C_182,D_183)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_454,plain,(
    ! [D_183] : k7_relset_1('#skF_3','#skF_2','#skF_4',D_183) = k9_relat_1('#skF_4',D_183) ),
    inference(resolution,[status(thm)],[c_28,c_451])).

tff(c_473,plain,(
    ! [A_191,B_192,C_193] :
      ( k7_relset_1(A_191,B_192,C_193,A_191) = k2_relset_1(A_191,B_192,C_193)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(A_191,B_192))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_475,plain,(
    k7_relset_1('#skF_3','#skF_2','#skF_4','#skF_3') = k2_relset_1('#skF_3','#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_473])).

tff(c_477,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k9_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_475])).

tff(c_34,plain,(
    ! [E_67] :
      ( ~ r2_hidden('#skF_5',k2_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ r2_hidden(k4_tarski(E_67,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(E_67,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_395,plain,(
    ~ r2_hidden('#skF_5',k2_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_479,plain,(
    ~ r2_hidden('#skF_5',k9_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_395])).

tff(c_840,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_832,c_479])).

tff(c_852,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_840])).

tff(c_854,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_852])).

tff(c_855,plain,(
    ! [E_67] :
      ( ~ r2_hidden(k4_tarski(E_67,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(E_67,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_972,plain,(
    ! [B_267] :
      ( ~ m1_subset_1('#skF_1'('#skF_7',B_267,'#skF_4'),'#skF_3')
      | ~ r2_hidden('#skF_7',k9_relat_1('#skF_4',B_267))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_965,c_855])).

tff(c_1029,plain,(
    ! [B_275] :
      ( ~ m1_subset_1('#skF_1'('#skF_7',B_275,'#skF_4'),'#skF_3')
      | ~ r2_hidden('#skF_7',k9_relat_1('#skF_4',B_275)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_972])).

tff(c_1032,plain,(
    ~ m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_940,c_1029])).

tff(c_1039,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_952,c_1032])).

tff(c_1040,plain,(
    m1_subset_1('#skF_6','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1041,plain,(
    ~ r2_hidden('#skF_7',k2_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,
    ( r2_hidden(k4_tarski('#skF_6','#skF_5'),'#skF_4')
    | r2_hidden('#skF_7',k2_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1053,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1041,c_42])).

tff(c_1056,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1053,c_20])).

tff(c_1062,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1056])).

tff(c_1199,plain,(
    ! [A_317,C_318,B_319,D_320] :
      ( r2_hidden(A_317,k9_relat_1(C_318,B_319))
      | ~ r2_hidden(D_320,B_319)
      | ~ r2_hidden(k4_tarski(D_320,A_317),C_318)
      | ~ r2_hidden(D_320,k1_relat_1(C_318))
      | ~ v1_relat_1(C_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1338,plain,(
    ! [A_336,C_337,B_338,A_339] :
      ( r2_hidden(A_336,k9_relat_1(C_337,B_338))
      | ~ r2_hidden(k4_tarski(A_339,A_336),C_337)
      | ~ r2_hidden(A_339,k1_relat_1(C_337))
      | ~ v1_relat_1(C_337)
      | v1_xboole_0(B_338)
      | ~ m1_subset_1(A_339,B_338) ) ),
    inference(resolution,[status(thm)],[c_4,c_1199])).

tff(c_1348,plain,(
    ! [B_338] :
      ( r2_hidden('#skF_5',k9_relat_1('#skF_4',B_338))
      | ~ r2_hidden('#skF_6',k1_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4')
      | v1_xboole_0(B_338)
      | ~ m1_subset_1('#skF_6',B_338) ) ),
    inference(resolution,[status(thm)],[c_1053,c_1338])).

tff(c_1359,plain,(
    ! [B_340] :
      ( r2_hidden('#skF_5',k9_relat_1('#skF_4',B_340))
      | v1_xboole_0(B_340)
      | ~ m1_subset_1('#skF_6',B_340) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1062,c_1348])).

tff(c_1118,plain,(
    ! [A_294,B_295,C_296,D_297] :
      ( k7_relset_1(A_294,B_295,C_296,D_297) = k9_relat_1(C_296,D_297)
      | ~ m1_subset_1(C_296,k1_zfmisc_1(k2_zfmisc_1(A_294,B_295))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1121,plain,(
    ! [D_297] : k7_relset_1('#skF_3','#skF_2','#skF_4',D_297) = k9_relat_1('#skF_4',D_297) ),
    inference(resolution,[status(thm)],[c_28,c_1118])).

tff(c_1178,plain,(
    ! [A_314,B_315,C_316] :
      ( k7_relset_1(A_314,B_315,C_316,A_314) = k2_relset_1(A_314,B_315,C_316)
      | ~ m1_subset_1(C_316,k1_zfmisc_1(k2_zfmisc_1(A_314,B_315))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1180,plain,(
    k7_relset_1('#skF_3','#skF_2','#skF_4','#skF_3') = k2_relset_1('#skF_3','#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_1178])).

tff(c_1182,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k9_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1121,c_1180])).

tff(c_40,plain,
    ( ~ r2_hidden('#skF_5',k2_relset_1('#skF_3','#skF_2','#skF_4'))
    | r2_hidden('#skF_7',k2_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1084,plain,(
    ~ r2_hidden('#skF_5',k2_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_1041,c_40])).

tff(c_1185,plain,(
    ~ r2_hidden('#skF_5',k9_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1182,c_1084])).

tff(c_1364,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_1359,c_1185])).

tff(c_1376,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1040,c_1364])).

tff(c_1378,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1376])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:18:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.56/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.67  
% 3.56/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.67  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 3.56/1.67  
% 3.56/1.67  %Foreground sorts:
% 3.56/1.67  
% 3.56/1.67  
% 3.56/1.67  %Background operators:
% 3.56/1.67  
% 3.56/1.67  
% 3.56/1.67  %Foreground operators:
% 3.56/1.67  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.56/1.67  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.56/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.56/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.56/1.67  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.56/1.67  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.56/1.67  tff('#skF_7', type, '#skF_7': $i).
% 3.56/1.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.56/1.67  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.56/1.67  tff('#skF_5', type, '#skF_5': $i).
% 3.56/1.67  tff('#skF_6', type, '#skF_6': $i).
% 3.56/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.56/1.67  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.56/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.56/1.67  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.56/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.56/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.56/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.56/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.56/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.56/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.56/1.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.56/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.56/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.56/1.67  
% 3.56/1.70  tff(f_92, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (![D]: (r2_hidden(D, k2_relset_1(B, A, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(E, D), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relset_1)).
% 3.56/1.70  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.56/1.70  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.56/1.70  tff(f_67, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.56/1.70  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 3.56/1.70  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 3.56/1.70  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.56/1.70  tff(f_63, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 3.56/1.70  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.56/1.70  tff(c_30, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.56/1.70  tff(c_8, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.56/1.70  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.56/1.70  tff(c_52, plain, (![B_74, A_75]: (v1_relat_1(B_74) | ~m1_subset_1(B_74, k1_zfmisc_1(A_75)) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.56/1.70  tff(c_55, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_52])).
% 3.56/1.70  tff(c_58, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_55])).
% 3.56/1.70  tff(c_898, plain, (![A_246, B_247, C_248, D_249]: (k7_relset_1(A_246, B_247, C_248, D_249)=k9_relat_1(C_248, D_249) | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(A_246, B_247))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.56/1.70  tff(c_901, plain, (![D_249]: (k7_relset_1('#skF_3', '#skF_2', '#skF_4', D_249)=k9_relat_1('#skF_4', D_249))), inference(resolution, [status(thm)], [c_28, c_898])).
% 3.56/1.70  tff(c_932, plain, (![A_263, B_264, C_265]: (k7_relset_1(A_263, B_264, C_265, A_263)=k2_relset_1(A_263, B_264, C_265) | ~m1_subset_1(C_265, k1_zfmisc_1(k2_zfmisc_1(A_263, B_264))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.56/1.70  tff(c_934, plain, (k7_relset_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')=k2_relset_1('#skF_3', '#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_932])).
% 3.56/1.70  tff(c_936, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k9_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_901, c_934])).
% 3.56/1.70  tff(c_44, plain, (m1_subset_1('#skF_6', '#skF_3') | r2_hidden('#skF_7', k2_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.56/1.70  tff(c_59, plain, (r2_hidden('#skF_7', k2_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_44])).
% 3.56/1.70  tff(c_940, plain, (r2_hidden('#skF_7', k9_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_936, c_59])).
% 3.56/1.70  tff(c_230, plain, (![A_126, B_127, C_128]: (r2_hidden('#skF_1'(A_126, B_127, C_128), B_127) | ~r2_hidden(A_126, k9_relat_1(C_128, B_127)) | ~v1_relat_1(C_128))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.56/1.70  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.56/1.70  tff(c_234, plain, (![A_126, B_127, C_128]: (m1_subset_1('#skF_1'(A_126, B_127, C_128), B_127) | ~r2_hidden(A_126, k9_relat_1(C_128, B_127)) | ~v1_relat_1(C_128))), inference(resolution, [status(thm)], [c_230, c_2])).
% 3.56/1.70  tff(c_946, plain, (m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_940, c_234])).
% 3.56/1.70  tff(c_952, plain, (m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_946])).
% 3.56/1.70  tff(c_965, plain, (![A_266, B_267, C_268]: (r2_hidden(k4_tarski('#skF_1'(A_266, B_267, C_268), A_266), C_268) | ~r2_hidden(A_266, k9_relat_1(C_268, B_267)) | ~v1_relat_1(C_268))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.56/1.70  tff(c_107, plain, (![A_99, B_100, C_101, D_102]: (k7_relset_1(A_99, B_100, C_101, D_102)=k9_relat_1(C_101, D_102) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.56/1.70  tff(c_110, plain, (![D_102]: (k7_relset_1('#skF_3', '#skF_2', '#skF_4', D_102)=k9_relat_1('#skF_4', D_102))), inference(resolution, [status(thm)], [c_28, c_107])).
% 3.56/1.70  tff(c_121, plain, (![A_107, B_108, C_109]: (k7_relset_1(A_107, B_108, C_109, A_107)=k2_relset_1(A_107, B_108, C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.56/1.70  tff(c_123, plain, (k7_relset_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')=k2_relset_1('#skF_3', '#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_121])).
% 3.56/1.70  tff(c_125, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k9_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_123])).
% 3.56/1.70  tff(c_127, plain, (r2_hidden('#skF_7', k9_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_59])).
% 3.56/1.70  tff(c_86, plain, (![A_84, B_85, C_86]: (r2_hidden('#skF_1'(A_84, B_85, C_86), B_85) | ~r2_hidden(A_84, k9_relat_1(C_86, B_85)) | ~v1_relat_1(C_86))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.56/1.70  tff(c_90, plain, (![A_84, B_85, C_86]: (m1_subset_1('#skF_1'(A_84, B_85, C_86), B_85) | ~r2_hidden(A_84, k9_relat_1(C_86, B_85)) | ~v1_relat_1(C_86))), inference(resolution, [status(thm)], [c_86, c_2])).
% 3.56/1.70  tff(c_133, plain, (m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_127, c_90])).
% 3.56/1.70  tff(c_139, plain, (m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_133])).
% 3.56/1.70  tff(c_142, plain, (![A_110, B_111, C_112]: (r2_hidden(k4_tarski('#skF_1'(A_110, B_111, C_112), A_110), C_112) | ~r2_hidden(A_110, k9_relat_1(C_112, B_111)) | ~v1_relat_1(C_112))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.56/1.70  tff(c_38, plain, (![E_67]: (m1_subset_1('#skF_6', '#skF_3') | ~r2_hidden(k4_tarski(E_67, '#skF_7'), '#skF_4') | ~m1_subset_1(E_67, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.56/1.70  tff(c_60, plain, (![E_67]: (~r2_hidden(k4_tarski(E_67, '#skF_7'), '#skF_4') | ~m1_subset_1(E_67, '#skF_3'))), inference(splitLeft, [status(thm)], [c_38])).
% 3.56/1.70  tff(c_155, plain, (![B_111]: (~m1_subset_1('#skF_1'('#skF_7', B_111, '#skF_4'), '#skF_3') | ~r2_hidden('#skF_7', k9_relat_1('#skF_4', B_111)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_142, c_60])).
% 3.56/1.70  tff(c_200, plain, (![B_119]: (~m1_subset_1('#skF_1'('#skF_7', B_119, '#skF_4'), '#skF_3') | ~r2_hidden('#skF_7', k9_relat_1('#skF_4', B_119)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_155])).
% 3.56/1.70  tff(c_203, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_127, c_200])).
% 3.56/1.70  tff(c_210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_203])).
% 3.56/1.70  tff(c_211, plain, (m1_subset_1('#skF_6', '#skF_3')), inference(splitRight, [status(thm)], [c_38])).
% 3.56/1.70  tff(c_256, plain, (![A_140, B_141, C_142, D_143]: (k7_relset_1(A_140, B_141, C_142, D_143)=k9_relat_1(C_142, D_143) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.56/1.70  tff(c_259, plain, (![D_143]: (k7_relset_1('#skF_3', '#skF_2', '#skF_4', D_143)=k9_relat_1('#skF_4', D_143))), inference(resolution, [status(thm)], [c_28, c_256])).
% 3.56/1.70  tff(c_332, plain, (![A_161, B_162, C_163]: (k7_relset_1(A_161, B_162, C_163, A_161)=k2_relset_1(A_161, B_162, C_163) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.56/1.70  tff(c_334, plain, (k7_relset_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')=k2_relset_1('#skF_3', '#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_332])).
% 3.56/1.70  tff(c_336, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k9_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_259, c_334])).
% 3.56/1.70  tff(c_340, plain, (r2_hidden('#skF_7', k9_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_336, c_59])).
% 3.56/1.70  tff(c_356, plain, (m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_340, c_234])).
% 3.56/1.70  tff(c_366, plain, (m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_356])).
% 3.56/1.70  tff(c_287, plain, (![A_154, B_155, C_156]: (r2_hidden(k4_tarski('#skF_1'(A_154, B_155, C_156), A_154), C_156) | ~r2_hidden(A_154, k9_relat_1(C_156, B_155)) | ~v1_relat_1(C_156))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.56/1.70  tff(c_36, plain, (![E_67]: (r2_hidden(k4_tarski('#skF_6', '#skF_5'), '#skF_4') | ~r2_hidden(k4_tarski(E_67, '#skF_7'), '#skF_4') | ~m1_subset_1(E_67, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.56/1.70  tff(c_235, plain, (![E_67]: (~r2_hidden(k4_tarski(E_67, '#skF_7'), '#skF_4') | ~m1_subset_1(E_67, '#skF_3'))), inference(splitLeft, [status(thm)], [c_36])).
% 3.56/1.70  tff(c_294, plain, (![B_155]: (~m1_subset_1('#skF_1'('#skF_7', B_155, '#skF_4'), '#skF_3') | ~r2_hidden('#skF_7', k9_relat_1('#skF_4', B_155)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_287, c_235])).
% 3.56/1.70  tff(c_307, plain, (![B_155]: (~m1_subset_1('#skF_1'('#skF_7', B_155, '#skF_4'), '#skF_3') | ~r2_hidden('#skF_7', k9_relat_1('#skF_4', B_155)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_294])).
% 3.56/1.70  tff(c_360, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_340, c_307])).
% 3.56/1.70  tff(c_393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_366, c_360])).
% 3.56/1.70  tff(c_394, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_36])).
% 3.56/1.70  tff(c_20, plain, (![A_16, C_18, B_17]: (r2_hidden(A_16, k1_relat_1(C_18)) | ~r2_hidden(k4_tarski(A_16, B_17), C_18) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.56/1.70  tff(c_398, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_394, c_20])).
% 3.56/1.70  tff(c_407, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_398])).
% 3.56/1.70  tff(c_4, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.56/1.70  tff(c_599, plain, (![A_209, C_210, B_211, D_212]: (r2_hidden(A_209, k9_relat_1(C_210, B_211)) | ~r2_hidden(D_212, B_211) | ~r2_hidden(k4_tarski(D_212, A_209), C_210) | ~r2_hidden(D_212, k1_relat_1(C_210)) | ~v1_relat_1(C_210))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.56/1.70  tff(c_803, plain, (![A_236, C_237, B_238, A_239]: (r2_hidden(A_236, k9_relat_1(C_237, B_238)) | ~r2_hidden(k4_tarski(A_239, A_236), C_237) | ~r2_hidden(A_239, k1_relat_1(C_237)) | ~v1_relat_1(C_237) | v1_xboole_0(B_238) | ~m1_subset_1(A_239, B_238))), inference(resolution, [status(thm)], [c_4, c_599])).
% 3.56/1.70  tff(c_819, plain, (![B_238]: (r2_hidden('#skF_5', k9_relat_1('#skF_4', B_238)) | ~r2_hidden('#skF_6', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | v1_xboole_0(B_238) | ~m1_subset_1('#skF_6', B_238))), inference(resolution, [status(thm)], [c_394, c_803])).
% 3.56/1.70  tff(c_832, plain, (![B_240]: (r2_hidden('#skF_5', k9_relat_1('#skF_4', B_240)) | v1_xboole_0(B_240) | ~m1_subset_1('#skF_6', B_240))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_407, c_819])).
% 3.56/1.70  tff(c_451, plain, (![A_180, B_181, C_182, D_183]: (k7_relset_1(A_180, B_181, C_182, D_183)=k9_relat_1(C_182, D_183) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.56/1.70  tff(c_454, plain, (![D_183]: (k7_relset_1('#skF_3', '#skF_2', '#skF_4', D_183)=k9_relat_1('#skF_4', D_183))), inference(resolution, [status(thm)], [c_28, c_451])).
% 3.56/1.70  tff(c_473, plain, (![A_191, B_192, C_193]: (k7_relset_1(A_191, B_192, C_193, A_191)=k2_relset_1(A_191, B_192, C_193) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(A_191, B_192))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.56/1.70  tff(c_475, plain, (k7_relset_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')=k2_relset_1('#skF_3', '#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_473])).
% 3.56/1.70  tff(c_477, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k9_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_454, c_475])).
% 3.56/1.70  tff(c_34, plain, (![E_67]: (~r2_hidden('#skF_5', k2_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~r2_hidden(k4_tarski(E_67, '#skF_7'), '#skF_4') | ~m1_subset_1(E_67, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.56/1.70  tff(c_395, plain, (~r2_hidden('#skF_5', k2_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_34])).
% 3.56/1.70  tff(c_479, plain, (~r2_hidden('#skF_5', k9_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_477, c_395])).
% 3.56/1.70  tff(c_840, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_832, c_479])).
% 3.56/1.70  tff(c_852, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_211, c_840])).
% 3.56/1.70  tff(c_854, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_852])).
% 3.56/1.70  tff(c_855, plain, (![E_67]: (~r2_hidden(k4_tarski(E_67, '#skF_7'), '#skF_4') | ~m1_subset_1(E_67, '#skF_3'))), inference(splitRight, [status(thm)], [c_34])).
% 3.56/1.70  tff(c_972, plain, (![B_267]: (~m1_subset_1('#skF_1'('#skF_7', B_267, '#skF_4'), '#skF_3') | ~r2_hidden('#skF_7', k9_relat_1('#skF_4', B_267)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_965, c_855])).
% 3.56/1.70  tff(c_1029, plain, (![B_275]: (~m1_subset_1('#skF_1'('#skF_7', B_275, '#skF_4'), '#skF_3') | ~r2_hidden('#skF_7', k9_relat_1('#skF_4', B_275)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_972])).
% 3.56/1.70  tff(c_1032, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_940, c_1029])).
% 3.56/1.70  tff(c_1039, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_952, c_1032])).
% 3.56/1.70  tff(c_1040, plain, (m1_subset_1('#skF_6', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 3.56/1.70  tff(c_1041, plain, (~r2_hidden('#skF_7', k2_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_44])).
% 3.56/1.70  tff(c_42, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_5'), '#skF_4') | r2_hidden('#skF_7', k2_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.56/1.70  tff(c_1053, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1041, c_42])).
% 3.56/1.70  tff(c_1056, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1053, c_20])).
% 3.56/1.70  tff(c_1062, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1056])).
% 3.56/1.70  tff(c_1199, plain, (![A_317, C_318, B_319, D_320]: (r2_hidden(A_317, k9_relat_1(C_318, B_319)) | ~r2_hidden(D_320, B_319) | ~r2_hidden(k4_tarski(D_320, A_317), C_318) | ~r2_hidden(D_320, k1_relat_1(C_318)) | ~v1_relat_1(C_318))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.56/1.70  tff(c_1338, plain, (![A_336, C_337, B_338, A_339]: (r2_hidden(A_336, k9_relat_1(C_337, B_338)) | ~r2_hidden(k4_tarski(A_339, A_336), C_337) | ~r2_hidden(A_339, k1_relat_1(C_337)) | ~v1_relat_1(C_337) | v1_xboole_0(B_338) | ~m1_subset_1(A_339, B_338))), inference(resolution, [status(thm)], [c_4, c_1199])).
% 3.56/1.70  tff(c_1348, plain, (![B_338]: (r2_hidden('#skF_5', k9_relat_1('#skF_4', B_338)) | ~r2_hidden('#skF_6', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | v1_xboole_0(B_338) | ~m1_subset_1('#skF_6', B_338))), inference(resolution, [status(thm)], [c_1053, c_1338])).
% 3.56/1.70  tff(c_1359, plain, (![B_340]: (r2_hidden('#skF_5', k9_relat_1('#skF_4', B_340)) | v1_xboole_0(B_340) | ~m1_subset_1('#skF_6', B_340))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1062, c_1348])).
% 3.56/1.70  tff(c_1118, plain, (![A_294, B_295, C_296, D_297]: (k7_relset_1(A_294, B_295, C_296, D_297)=k9_relat_1(C_296, D_297) | ~m1_subset_1(C_296, k1_zfmisc_1(k2_zfmisc_1(A_294, B_295))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.56/1.70  tff(c_1121, plain, (![D_297]: (k7_relset_1('#skF_3', '#skF_2', '#skF_4', D_297)=k9_relat_1('#skF_4', D_297))), inference(resolution, [status(thm)], [c_28, c_1118])).
% 3.56/1.70  tff(c_1178, plain, (![A_314, B_315, C_316]: (k7_relset_1(A_314, B_315, C_316, A_314)=k2_relset_1(A_314, B_315, C_316) | ~m1_subset_1(C_316, k1_zfmisc_1(k2_zfmisc_1(A_314, B_315))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.56/1.70  tff(c_1180, plain, (k7_relset_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')=k2_relset_1('#skF_3', '#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_1178])).
% 3.56/1.70  tff(c_1182, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k9_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1121, c_1180])).
% 3.56/1.70  tff(c_40, plain, (~r2_hidden('#skF_5', k2_relset_1('#skF_3', '#skF_2', '#skF_4')) | r2_hidden('#skF_7', k2_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.56/1.70  tff(c_1084, plain, (~r2_hidden('#skF_5', k2_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1041, c_40])).
% 3.56/1.70  tff(c_1185, plain, (~r2_hidden('#skF_5', k9_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1182, c_1084])).
% 3.56/1.70  tff(c_1364, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_1359, c_1185])).
% 3.56/1.70  tff(c_1376, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1040, c_1364])).
% 3.56/1.70  tff(c_1378, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_1376])).
% 3.56/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.70  
% 3.56/1.70  Inference rules
% 3.56/1.70  ----------------------
% 3.56/1.70  #Ref     : 0
% 3.56/1.70  #Sup     : 294
% 3.56/1.70  #Fact    : 0
% 3.56/1.70  #Define  : 0
% 3.56/1.70  #Split   : 12
% 3.56/1.70  #Chain   : 0
% 3.56/1.70  #Close   : 0
% 3.56/1.70  
% 3.56/1.70  Ordering : KBO
% 3.56/1.70  
% 3.56/1.70  Simplification rules
% 3.56/1.70  ----------------------
% 3.56/1.70  #Subsume      : 26
% 3.56/1.70  #Demod        : 80
% 3.56/1.70  #Tautology    : 51
% 3.56/1.70  #SimpNegUnit  : 4
% 3.56/1.70  #BackRed      : 18
% 3.56/1.70  
% 3.56/1.70  #Partial instantiations: 0
% 3.56/1.70  #Strategies tried      : 1
% 3.56/1.70  
% 3.56/1.70  Timing (in seconds)
% 3.56/1.70  ----------------------
% 3.94/1.70  Preprocessing        : 0.33
% 3.94/1.70  Parsing              : 0.18
% 3.94/1.70  CNF conversion       : 0.03
% 3.94/1.70  Main loop            : 0.52
% 3.94/1.70  Inferencing          : 0.21
% 3.94/1.70  Reduction            : 0.15
% 3.94/1.70  Demodulation         : 0.10
% 3.94/1.70  BG Simplification    : 0.02
% 3.94/1.70  Subsumption          : 0.09
% 3.94/1.70  Abstraction          : 0.03
% 3.94/1.70  MUC search           : 0.00
% 3.94/1.70  Cooper               : 0.00
% 3.94/1.70  Total                : 0.90
% 3.94/1.70  Index Insertion      : 0.00
% 3.94/1.70  Index Deletion       : 0.00
% 3.94/1.70  Index Matching       : 0.00
% 3.94/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------

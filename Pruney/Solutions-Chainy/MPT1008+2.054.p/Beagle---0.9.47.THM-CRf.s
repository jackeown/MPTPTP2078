%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:33 EST 2020

% Result     : Theorem 3.66s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 333 expanded)
%              Number of leaves         :   45 ( 129 expanded)
%              Depth                    :   16
%              Number of atoms          :  166 ( 669 expanded)
%              Number of equality atoms :   80 ( 275 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_108,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_127,plain,(
    ! [C_79,A_80,B_81] :
      ( v1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_136,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_127])).

tff(c_68,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_40,plain,(
    ! [A_38] :
      ( k1_relat_1(A_38) != k1_xboole_0
      | k1_xboole_0 = A_38
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_143,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_136,c_40])).

tff(c_145,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_143])).

tff(c_347,plain,(
    ! [B_133,A_134] :
      ( k1_tarski(k1_funct_1(B_133,A_134)) = k2_relat_1(B_133)
      | k1_tarski(A_134) != k1_relat_1(B_133)
      | ~ v1_funct_1(B_133)
      | ~ v1_relat_1(B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_300,plain,(
    ! [A_120,B_121,C_122] :
      ( k2_relset_1(A_120,B_121,C_122) = k2_relat_1(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_309,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_300])).

tff(c_60,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') != k1_tarski(k1_funct_1('#skF_3','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_310,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_60])).

tff(c_353,plain,
    ( k1_tarski('#skF_1') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_310])).

tff(c_372,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_68,c_353])).

tff(c_178,plain,(
    ! [C_90,A_91,B_92] :
      ( v4_relat_1(C_90,A_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_187,plain,(
    v4_relat_1('#skF_3',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_178])).

tff(c_36,plain,(
    ! [B_37,A_36] :
      ( r1_tarski(k1_relat_1(B_37),A_36)
      | ~ v4_relat_1(B_37,A_36)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_655,plain,(
    ! [B_188,C_189,A_190] :
      ( k2_tarski(B_188,C_189) = A_190
      | k1_tarski(C_189) = A_190
      | k1_tarski(B_188) = A_190
      | k1_xboole_0 = A_190
      | ~ r1_tarski(A_190,k2_tarski(B_188,C_189)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_675,plain,(
    ! [A_3,A_190] :
      ( k2_tarski(A_3,A_3) = A_190
      | k1_tarski(A_3) = A_190
      | k1_tarski(A_3) = A_190
      | k1_xboole_0 = A_190
      | ~ r1_tarski(A_190,k1_tarski(A_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_655])).

tff(c_700,plain,(
    ! [A_194,A_195] :
      ( k1_tarski(A_194) = A_195
      | k1_tarski(A_194) = A_195
      | k1_tarski(A_194) = A_195
      | k1_xboole_0 = A_195
      | ~ r1_tarski(A_195,k1_tarski(A_194)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_675])).

tff(c_754,plain,(
    ! [A_197,B_198] :
      ( k1_tarski(A_197) = k1_relat_1(B_198)
      | k1_relat_1(B_198) = k1_xboole_0
      | ~ v4_relat_1(B_198,k1_tarski(A_197))
      | ~ v1_relat_1(B_198) ) ),
    inference(resolution,[status(thm)],[c_36,c_700])).

tff(c_764,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_3')
    | k1_relat_1('#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_187,c_754])).

tff(c_770,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_3')
    | k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_764])).

tff(c_772,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_372,c_770])).

tff(c_773,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_774,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_785,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_773,c_774])).

tff(c_986,plain,(
    ! [B_254,A_255] :
      ( k1_tarski(k1_funct_1(B_254,A_255)) = k2_relat_1(B_254)
      | k1_tarski(A_255) != k1_relat_1(B_254)
      | ~ v1_funct_1(B_254)
      | ~ v1_relat_1(B_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_943,plain,(
    ! [A_241,B_242,C_243] :
      ( k2_relset_1(A_241,B_242,C_243) = k2_relat_1(C_243)
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(A_241,B_242))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_952,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_943])).

tff(c_953,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_952,c_60])).

tff(c_992,plain,
    ( k1_tarski('#skF_1') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_986,c_953])).

tff(c_1011,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_68,c_785,c_992])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_780,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_773,c_62])).

tff(c_66,plain,(
    v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_779,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_773,c_2])).

tff(c_32,plain,(
    ! [A_34,B_35] :
      ( m1_subset_1(A_34,k1_zfmisc_1(B_35))
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1013,plain,(
    ! [A_256,B_257,C_258,D_259] :
      ( k8_relset_1(A_256,B_257,C_258,D_259) = k10_relat_1(C_258,D_259)
      | ~ m1_subset_1(C_258,k1_zfmisc_1(k2_zfmisc_1(A_256,B_257))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1070,plain,(
    ! [A_267,B_268,A_269,D_270] :
      ( k8_relset_1(A_267,B_268,A_269,D_270) = k10_relat_1(A_269,D_270)
      | ~ r1_tarski(A_269,k2_zfmisc_1(A_267,B_268)) ) ),
    inference(resolution,[status(thm)],[c_32,c_1013])).

tff(c_1080,plain,(
    ! [A_271,B_272,D_273] : k8_relset_1(A_271,B_272,'#skF_3',D_273) = k10_relat_1('#skF_3',D_273) ),
    inference(resolution,[status(thm)],[c_779,c_1070])).

tff(c_50,plain,(
    ! [A_47,B_48,C_49,D_50] :
      ( m1_subset_1(k8_relset_1(A_47,B_48,C_49,D_50),k1_zfmisc_1(A_47))
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1092,plain,(
    ! [D_274,A_275,B_276] :
      ( m1_subset_1(k10_relat_1('#skF_3',D_274),k1_zfmisc_1(A_275))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_275,B_276))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1080,c_50])).

tff(c_1095,plain,(
    ! [D_274,A_275,B_276] :
      ( m1_subset_1(k10_relat_1('#skF_3',D_274),k1_zfmisc_1(A_275))
      | ~ r1_tarski('#skF_3',k2_zfmisc_1(A_275,B_276)) ) ),
    inference(resolution,[status(thm)],[c_32,c_1092])).

tff(c_1114,plain,(
    ! [D_283,A_284] : m1_subset_1(k10_relat_1('#skF_3',D_283),k1_zfmisc_1(A_284)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_779,c_1095])).

tff(c_30,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,B_35)
      | ~ m1_subset_1(A_34,k1_zfmisc_1(B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1190,plain,(
    ! [D_297,A_298] : r1_tarski(k10_relat_1('#skF_3',D_297),A_298) ),
    inference(resolution,[status(thm)],[c_1114,c_30])).

tff(c_4,plain,(
    ! [A_2] :
      ( k1_xboole_0 = A_2
      | ~ r1_tarski(A_2,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_778,plain,(
    ! [A_2] :
      ( A_2 = '#skF_3'
      | ~ r1_tarski(A_2,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_773,c_773,c_4])).

tff(c_1222,plain,(
    ! [D_297] : k10_relat_1('#skF_3',D_297) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1190,c_778])).

tff(c_1078,plain,(
    ! [A_267,B_268,D_270] : k8_relset_1(A_267,B_268,'#skF_3',D_270) = k10_relat_1('#skF_3',D_270) ),
    inference(resolution,[status(thm)],[c_779,c_1070])).

tff(c_1228,plain,(
    ! [A_267,B_268,D_270] : k8_relset_1(A_267,B_268,'#skF_3',D_270) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1222,c_1078])).

tff(c_1100,plain,(
    ! [D_274,A_275] : m1_subset_1(k10_relat_1('#skF_3',D_274),k1_zfmisc_1(A_275)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_779,c_1095])).

tff(c_1227,plain,(
    ! [A_275] : m1_subset_1('#skF_3',k1_zfmisc_1(A_275)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1222,c_1100])).

tff(c_58,plain,(
    ! [B_59,A_58,C_60] :
      ( k1_xboole_0 = B_59
      | k8_relset_1(A_58,B_59,C_60,B_59) = A_58
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | ~ v1_funct_2(C_60,A_58,B_59)
      | ~ v1_funct_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1346,plain,(
    ! [B_309,A_310,C_311] :
      ( B_309 = '#skF_3'
      | k8_relset_1(A_310,B_309,C_311,B_309) = A_310
      | ~ m1_subset_1(C_311,k1_zfmisc_1(k2_zfmisc_1(A_310,B_309)))
      | ~ v1_funct_2(C_311,A_310,B_309)
      | ~ v1_funct_1(C_311) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_773,c_58])).

tff(c_1349,plain,(
    ! [B_309,A_310] :
      ( B_309 = '#skF_3'
      | k8_relset_1(A_310,B_309,'#skF_3',B_309) = A_310
      | ~ v1_funct_2('#skF_3',A_310,B_309)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1227,c_1346])).

tff(c_1361,plain,(
    ! [B_312,A_313] :
      ( B_312 = '#skF_3'
      | A_313 = '#skF_3'
      | ~ v1_funct_2('#skF_3',A_313,B_312) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1228,c_1349])).

tff(c_1364,plain,
    ( '#skF_2' = '#skF_3'
    | k1_tarski('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_66,c_1361])).

tff(c_1368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1011,c_780,c_1364])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:10:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.66/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.60  
% 3.66/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.61  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.66/1.61  
% 3.66/1.61  %Foreground sorts:
% 3.66/1.61  
% 3.66/1.61  
% 3.66/1.61  %Background operators:
% 3.66/1.61  
% 3.66/1.61  
% 3.66/1.61  %Foreground operators:
% 3.66/1.61  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.66/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.66/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.66/1.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.66/1.61  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.66/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.66/1.61  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.66/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.66/1.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.66/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.66/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.66/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.66/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.66/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.66/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.66/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.66/1.61  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.66/1.61  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.66/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.66/1.61  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.66/1.61  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.66/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.66/1.61  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.66/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.66/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.66/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.66/1.61  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.66/1.61  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.66/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.66/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.66/1.61  
% 3.85/1.63  tff(f_132, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 3.85/1.63  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.85/1.63  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.85/1.63  tff(f_86, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.85/1.63  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.85/1.63  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.85/1.63  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.85/1.63  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.85/1.63  tff(f_60, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.85/1.63  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.85/1.63  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.85/1.63  tff(f_108, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.85/1.63  tff(f_100, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k8_relset_1(A, B, C, D), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 3.85/1.63  tff(f_31, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.85/1.63  tff(f_120, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_2)).
% 3.85/1.63  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.85/1.63  tff(c_127, plain, (![C_79, A_80, B_81]: (v1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.85/1.63  tff(c_136, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_127])).
% 3.85/1.63  tff(c_68, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.85/1.63  tff(c_40, plain, (![A_38]: (k1_relat_1(A_38)!=k1_xboole_0 | k1_xboole_0=A_38 | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.85/1.63  tff(c_143, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_136, c_40])).
% 3.85/1.63  tff(c_145, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_143])).
% 3.85/1.63  tff(c_347, plain, (![B_133, A_134]: (k1_tarski(k1_funct_1(B_133, A_134))=k2_relat_1(B_133) | k1_tarski(A_134)!=k1_relat_1(B_133) | ~v1_funct_1(B_133) | ~v1_relat_1(B_133))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.85/1.63  tff(c_300, plain, (![A_120, B_121, C_122]: (k2_relset_1(A_120, B_121, C_122)=k2_relat_1(C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.85/1.63  tff(c_309, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_300])).
% 3.85/1.63  tff(c_60, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')!=k1_tarski(k1_funct_1('#skF_3', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.85/1.63  tff(c_310, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_309, c_60])).
% 3.85/1.63  tff(c_353, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_347, c_310])).
% 3.85/1.63  tff(c_372, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_68, c_353])).
% 3.85/1.63  tff(c_178, plain, (![C_90, A_91, B_92]: (v4_relat_1(C_90, A_91) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.85/1.63  tff(c_187, plain, (v4_relat_1('#skF_3', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_64, c_178])).
% 3.85/1.63  tff(c_36, plain, (![B_37, A_36]: (r1_tarski(k1_relat_1(B_37), A_36) | ~v4_relat_1(B_37, A_36) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.85/1.63  tff(c_6, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.85/1.63  tff(c_655, plain, (![B_188, C_189, A_190]: (k2_tarski(B_188, C_189)=A_190 | k1_tarski(C_189)=A_190 | k1_tarski(B_188)=A_190 | k1_xboole_0=A_190 | ~r1_tarski(A_190, k2_tarski(B_188, C_189)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.85/1.63  tff(c_675, plain, (![A_3, A_190]: (k2_tarski(A_3, A_3)=A_190 | k1_tarski(A_3)=A_190 | k1_tarski(A_3)=A_190 | k1_xboole_0=A_190 | ~r1_tarski(A_190, k1_tarski(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_655])).
% 3.85/1.63  tff(c_700, plain, (![A_194, A_195]: (k1_tarski(A_194)=A_195 | k1_tarski(A_194)=A_195 | k1_tarski(A_194)=A_195 | k1_xboole_0=A_195 | ~r1_tarski(A_195, k1_tarski(A_194)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_675])).
% 3.85/1.63  tff(c_754, plain, (![A_197, B_198]: (k1_tarski(A_197)=k1_relat_1(B_198) | k1_relat_1(B_198)=k1_xboole_0 | ~v4_relat_1(B_198, k1_tarski(A_197)) | ~v1_relat_1(B_198))), inference(resolution, [status(thm)], [c_36, c_700])).
% 3.85/1.63  tff(c_764, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_3') | k1_relat_1('#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_187, c_754])).
% 3.85/1.63  tff(c_770, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_3') | k1_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_136, c_764])).
% 3.85/1.63  tff(c_772, plain, $false, inference(negUnitSimplification, [status(thm)], [c_145, c_372, c_770])).
% 3.85/1.63  tff(c_773, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_143])).
% 3.85/1.63  tff(c_774, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_143])).
% 3.85/1.63  tff(c_785, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_773, c_774])).
% 3.85/1.63  tff(c_986, plain, (![B_254, A_255]: (k1_tarski(k1_funct_1(B_254, A_255))=k2_relat_1(B_254) | k1_tarski(A_255)!=k1_relat_1(B_254) | ~v1_funct_1(B_254) | ~v1_relat_1(B_254))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.85/1.63  tff(c_943, plain, (![A_241, B_242, C_243]: (k2_relset_1(A_241, B_242, C_243)=k2_relat_1(C_243) | ~m1_subset_1(C_243, k1_zfmisc_1(k2_zfmisc_1(A_241, B_242))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.85/1.63  tff(c_952, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_943])).
% 3.85/1.63  tff(c_953, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_952, c_60])).
% 3.85/1.63  tff(c_992, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_986, c_953])).
% 3.85/1.63  tff(c_1011, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_136, c_68, c_785, c_992])).
% 3.85/1.63  tff(c_62, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.85/1.63  tff(c_780, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_773, c_62])).
% 3.85/1.63  tff(c_66, plain, (v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.85/1.63  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.85/1.63  tff(c_779, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_773, c_2])).
% 3.85/1.63  tff(c_32, plain, (![A_34, B_35]: (m1_subset_1(A_34, k1_zfmisc_1(B_35)) | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.85/1.63  tff(c_1013, plain, (![A_256, B_257, C_258, D_259]: (k8_relset_1(A_256, B_257, C_258, D_259)=k10_relat_1(C_258, D_259) | ~m1_subset_1(C_258, k1_zfmisc_1(k2_zfmisc_1(A_256, B_257))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.85/1.63  tff(c_1070, plain, (![A_267, B_268, A_269, D_270]: (k8_relset_1(A_267, B_268, A_269, D_270)=k10_relat_1(A_269, D_270) | ~r1_tarski(A_269, k2_zfmisc_1(A_267, B_268)))), inference(resolution, [status(thm)], [c_32, c_1013])).
% 3.85/1.63  tff(c_1080, plain, (![A_271, B_272, D_273]: (k8_relset_1(A_271, B_272, '#skF_3', D_273)=k10_relat_1('#skF_3', D_273))), inference(resolution, [status(thm)], [c_779, c_1070])).
% 3.85/1.63  tff(c_50, plain, (![A_47, B_48, C_49, D_50]: (m1_subset_1(k8_relset_1(A_47, B_48, C_49, D_50), k1_zfmisc_1(A_47)) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.85/1.63  tff(c_1092, plain, (![D_274, A_275, B_276]: (m1_subset_1(k10_relat_1('#skF_3', D_274), k1_zfmisc_1(A_275)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_275, B_276))))), inference(superposition, [status(thm), theory('equality')], [c_1080, c_50])).
% 3.85/1.63  tff(c_1095, plain, (![D_274, A_275, B_276]: (m1_subset_1(k10_relat_1('#skF_3', D_274), k1_zfmisc_1(A_275)) | ~r1_tarski('#skF_3', k2_zfmisc_1(A_275, B_276)))), inference(resolution, [status(thm)], [c_32, c_1092])).
% 3.85/1.63  tff(c_1114, plain, (![D_283, A_284]: (m1_subset_1(k10_relat_1('#skF_3', D_283), k1_zfmisc_1(A_284)))), inference(demodulation, [status(thm), theory('equality')], [c_779, c_1095])).
% 3.85/1.63  tff(c_30, plain, (![A_34, B_35]: (r1_tarski(A_34, B_35) | ~m1_subset_1(A_34, k1_zfmisc_1(B_35)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.85/1.63  tff(c_1190, plain, (![D_297, A_298]: (r1_tarski(k10_relat_1('#skF_3', D_297), A_298))), inference(resolution, [status(thm)], [c_1114, c_30])).
% 3.85/1.63  tff(c_4, plain, (![A_2]: (k1_xboole_0=A_2 | ~r1_tarski(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.85/1.63  tff(c_778, plain, (![A_2]: (A_2='#skF_3' | ~r1_tarski(A_2, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_773, c_773, c_4])).
% 3.85/1.63  tff(c_1222, plain, (![D_297]: (k10_relat_1('#skF_3', D_297)='#skF_3')), inference(resolution, [status(thm)], [c_1190, c_778])).
% 3.85/1.63  tff(c_1078, plain, (![A_267, B_268, D_270]: (k8_relset_1(A_267, B_268, '#skF_3', D_270)=k10_relat_1('#skF_3', D_270))), inference(resolution, [status(thm)], [c_779, c_1070])).
% 3.85/1.63  tff(c_1228, plain, (![A_267, B_268, D_270]: (k8_relset_1(A_267, B_268, '#skF_3', D_270)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1222, c_1078])).
% 3.85/1.63  tff(c_1100, plain, (![D_274, A_275]: (m1_subset_1(k10_relat_1('#skF_3', D_274), k1_zfmisc_1(A_275)))), inference(demodulation, [status(thm), theory('equality')], [c_779, c_1095])).
% 3.85/1.63  tff(c_1227, plain, (![A_275]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_275)))), inference(demodulation, [status(thm), theory('equality')], [c_1222, c_1100])).
% 3.85/1.63  tff(c_58, plain, (![B_59, A_58, C_60]: (k1_xboole_0=B_59 | k8_relset_1(A_58, B_59, C_60, B_59)=A_58 | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))) | ~v1_funct_2(C_60, A_58, B_59) | ~v1_funct_1(C_60))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.85/1.63  tff(c_1346, plain, (![B_309, A_310, C_311]: (B_309='#skF_3' | k8_relset_1(A_310, B_309, C_311, B_309)=A_310 | ~m1_subset_1(C_311, k1_zfmisc_1(k2_zfmisc_1(A_310, B_309))) | ~v1_funct_2(C_311, A_310, B_309) | ~v1_funct_1(C_311))), inference(demodulation, [status(thm), theory('equality')], [c_773, c_58])).
% 3.85/1.63  tff(c_1349, plain, (![B_309, A_310]: (B_309='#skF_3' | k8_relset_1(A_310, B_309, '#skF_3', B_309)=A_310 | ~v1_funct_2('#skF_3', A_310, B_309) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1227, c_1346])).
% 3.85/1.63  tff(c_1361, plain, (![B_312, A_313]: (B_312='#skF_3' | A_313='#skF_3' | ~v1_funct_2('#skF_3', A_313, B_312))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1228, c_1349])).
% 3.85/1.63  tff(c_1364, plain, ('#skF_2'='#skF_3' | k1_tarski('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_66, c_1361])).
% 3.85/1.63  tff(c_1368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1011, c_780, c_1364])).
% 3.85/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.63  
% 3.85/1.63  Inference rules
% 3.85/1.63  ----------------------
% 3.85/1.63  #Ref     : 0
% 3.85/1.63  #Sup     : 253
% 3.85/1.63  #Fact    : 1
% 3.85/1.63  #Define  : 0
% 3.85/1.63  #Split   : 5
% 3.85/1.63  #Chain   : 0
% 3.85/1.63  #Close   : 0
% 3.85/1.63  
% 3.85/1.63  Ordering : KBO
% 3.85/1.63  
% 3.85/1.63  Simplification rules
% 3.85/1.63  ----------------------
% 3.85/1.63  #Subsume      : 0
% 3.85/1.63  #Demod        : 175
% 3.85/1.63  #Tautology    : 157
% 3.85/1.63  #SimpNegUnit  : 2
% 3.85/1.63  #BackRed      : 15
% 3.85/1.63  
% 3.85/1.63  #Partial instantiations: 0
% 3.85/1.63  #Strategies tried      : 1
% 3.85/1.63  
% 3.85/1.63  Timing (in seconds)
% 3.85/1.63  ----------------------
% 3.85/1.63  Preprocessing        : 0.34
% 3.85/1.63  Parsing              : 0.18
% 3.85/1.63  CNF conversion       : 0.02
% 3.85/1.63  Main loop            : 0.45
% 3.85/1.63  Inferencing          : 0.17
% 3.85/1.63  Reduction            : 0.14
% 3.85/1.63  Demodulation         : 0.10
% 3.85/1.63  BG Simplification    : 0.03
% 3.85/1.63  Subsumption          : 0.06
% 3.85/1.63  Abstraction          : 0.03
% 3.85/1.63  MUC search           : 0.00
% 3.85/1.63  Cooper               : 0.00
% 3.85/1.63  Total                : 0.83
% 3.85/1.63  Index Insertion      : 0.00
% 3.85/1.63  Index Deletion       : 0.00
% 3.85/1.63  Index Matching       : 0.00
% 3.85/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------

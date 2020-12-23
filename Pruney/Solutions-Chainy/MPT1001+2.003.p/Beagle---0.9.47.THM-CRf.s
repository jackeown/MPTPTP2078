%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:55 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 149 expanded)
%              Number of leaves         :   32 (  64 expanded)
%              Depth                    :    8
%              Number of atoms          :  112 ( 306 expanded)
%              Number of equality atoms :   36 ( 101 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_relset_1 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & k8_relset_1(A,B,C,k1_tarski(D)) = k1_xboole_0 )
        <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k2_relat_1(B))
      <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_811,plain,(
    ! [C_175,A_176,B_177] :
      ( v1_relat_1(C_175)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_820,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_811])).

tff(c_416,plain,(
    ! [A_115,B_116,C_117] :
      ( k2_relset_1(A_115,B_116,C_117) = k2_relat_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_425,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_416])).

tff(c_42,plain,
    ( k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_70,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_441,plain,(
    k2_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_70])).

tff(c_26,plain,(
    ! [A_16,B_17,C_18] :
      ( m1_subset_1(k2_relset_1(A_16,B_17,C_18),k1_zfmisc_1(B_17))
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_445,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_26])).

tff(c_449,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_445])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_454,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_449,c_16])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_458,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_454,c_8])).

tff(c_463,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_441,c_458])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_72,plain,(
    ! [C_35,A_36,B_37] :
      ( v1_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_81,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_72])).

tff(c_367,plain,(
    ! [A_104,B_105] :
      ( r2_hidden(A_104,k2_relat_1(B_105))
      | k10_relat_1(B_105,k1_tarski(A_104)) = k1_xboole_0
      | ~ v1_relat_1(B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_713,plain,(
    ! [A_170,B_171] :
      ( r1_tarski(A_170,k2_relat_1(B_171))
      | k10_relat_1(B_171,k1_tarski('#skF_1'(A_170,k2_relat_1(B_171)))) = k1_xboole_0
      | ~ v1_relat_1(B_171) ) ),
    inference(resolution,[status(thm)],[c_367,c_4])).

tff(c_500,plain,(
    ! [A_129,B_130,C_131,D_132] :
      ( k8_relset_1(A_129,B_130,C_131,D_132) = k10_relat_1(C_131,D_132)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_511,plain,(
    ! [D_132] : k8_relset_1('#skF_2','#skF_3','#skF_4',D_132) = k10_relat_1('#skF_4',D_132) ),
    inference(resolution,[status(thm)],[c_32,c_500])).

tff(c_48,plain,(
    ! [D_28] :
      ( k8_relset_1('#skF_2','#skF_3','#skF_4',k1_tarski(D_28)) != k1_xboole_0
      | ~ r2_hidden(D_28,'#skF_3')
      | k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_384,plain,(
    ! [D_28] :
      ( k8_relset_1('#skF_2','#skF_3','#skF_4',k1_tarski(D_28)) != k1_xboole_0
      | ~ r2_hidden(D_28,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_48])).

tff(c_512,plain,(
    ! [D_28] :
      ( k10_relat_1('#skF_4',k1_tarski(D_28)) != k1_xboole_0
      | ~ r2_hidden(D_28,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_384])).

tff(c_732,plain,(
    ! [A_170] :
      ( ~ r2_hidden('#skF_1'(A_170,k2_relat_1('#skF_4')),'#skF_3')
      | r1_tarski(A_170,k2_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_713,c_512])).

tff(c_764,plain,(
    ! [A_174] :
      ( ~ r2_hidden('#skF_1'(A_174,k2_relat_1('#skF_4')),'#skF_3')
      | r1_tarski(A_174,k2_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_732])).

tff(c_780,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_764])).

tff(c_790,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_463,c_463,c_780])).

tff(c_792,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_912,plain,(
    ! [A_203,B_204,C_205] :
      ( k2_relset_1(A_203,B_204,C_205) = k2_relat_1(C_205)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_203,B_204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_919,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_912])).

tff(c_922,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_792,c_919])).

tff(c_791,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_852,plain,(
    ! [C_189,B_190,A_191] :
      ( r2_hidden(C_189,B_190)
      | ~ r2_hidden(C_189,A_191)
      | ~ r1_tarski(A_191,B_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_858,plain,(
    ! [B_190] :
      ( r2_hidden('#skF_5',B_190)
      | ~ r1_tarski('#skF_3',B_190) ) ),
    inference(resolution,[status(thm)],[c_791,c_852])).

tff(c_882,plain,(
    ! [B_197,A_198] :
      ( k10_relat_1(B_197,k1_tarski(A_198)) != k1_xboole_0
      | ~ r2_hidden(A_198,k2_relat_1(B_197))
      | ~ v1_relat_1(B_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_895,plain,(
    ! [B_197] :
      ( k10_relat_1(B_197,k1_tarski('#skF_5')) != k1_xboole_0
      | ~ v1_relat_1(B_197)
      | ~ r1_tarski('#skF_3',k2_relat_1(B_197)) ) ),
    inference(resolution,[status(thm)],[c_858,c_882])).

tff(c_926,plain,
    ( k10_relat_1('#skF_4',k1_tarski('#skF_5')) != k1_xboole_0
    | ~ v1_relat_1('#skF_4')
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_922,c_895])).

tff(c_936,plain,(
    k10_relat_1('#skF_4',k1_tarski('#skF_5')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_820,c_926])).

tff(c_1010,plain,(
    ! [A_216,B_217,C_218,D_219] :
      ( k8_relset_1(A_216,B_217,C_218,D_219) = k10_relat_1(C_218,D_219)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(A_216,B_217))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1022,plain,(
    ! [D_220] : k8_relset_1('#skF_2','#skF_3','#skF_4',D_220) = k10_relat_1('#skF_4',D_220) ),
    inference(resolution,[status(thm)],[c_32,c_1010])).

tff(c_38,plain,
    ( k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | k8_relset_1('#skF_2','#skF_3','#skF_4',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_793,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_799,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_792,c_793])).

tff(c_800,plain,(
    k8_relset_1('#skF_2','#skF_3','#skF_4',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1028,plain,(
    k10_relat_1('#skF_4',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1022,c_800])).

tff(c_1037,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_936,c_1028])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:23:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.46  
% 2.87/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.46  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_relset_1 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.87/1.46  
% 2.87/1.46  %Foreground sorts:
% 2.87/1.46  
% 2.87/1.46  
% 2.87/1.46  %Background operators:
% 2.87/1.46  
% 2.87/1.46  
% 2.87/1.46  %Foreground operators:
% 2.87/1.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.87/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.87/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.87/1.46  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.87/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.87/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.87/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.87/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.87/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.87/1.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.87/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.87/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.87/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.87/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.46  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.87/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.87/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.87/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.87/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.87/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.87/1.46  
% 3.13/1.47  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.13/1.47  tff(f_82, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (k8_relset_1(A, B, C, k1_tarski(D)) = k1_xboole_0))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_funct_2)).
% 3.13/1.47  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.13/1.47  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.13/1.47  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.13/1.47  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.13/1.47  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.13/1.47  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 3.13/1.47  tff(f_67, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.13/1.47  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.13/1.47  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.13/1.47  tff(c_811, plain, (![C_175, A_176, B_177]: (v1_relat_1(C_175) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.13/1.47  tff(c_820, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_811])).
% 3.13/1.47  tff(c_416, plain, (![A_115, B_116, C_117]: (k2_relset_1(A_115, B_116, C_117)=k2_relat_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.13/1.47  tff(c_425, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_416])).
% 3.13/1.47  tff(c_42, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.13/1.47  tff(c_70, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_42])).
% 3.13/1.47  tff(c_441, plain, (k2_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_425, c_70])).
% 3.13/1.47  tff(c_26, plain, (![A_16, B_17, C_18]: (m1_subset_1(k2_relset_1(A_16, B_17, C_18), k1_zfmisc_1(B_17)) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.13/1.47  tff(c_445, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_425, c_26])).
% 3.13/1.47  tff(c_449, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_445])).
% 3.13/1.47  tff(c_16, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.13/1.47  tff(c_454, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_449, c_16])).
% 3.13/1.47  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.13/1.47  tff(c_458, plain, (k2_relat_1('#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_454, c_8])).
% 3.13/1.47  tff(c_463, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_441, c_458])).
% 3.13/1.47  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.13/1.47  tff(c_72, plain, (![C_35, A_36, B_37]: (v1_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.13/1.47  tff(c_81, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_72])).
% 3.13/1.47  tff(c_367, plain, (![A_104, B_105]: (r2_hidden(A_104, k2_relat_1(B_105)) | k10_relat_1(B_105, k1_tarski(A_104))=k1_xboole_0 | ~v1_relat_1(B_105))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.13/1.47  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.13/1.47  tff(c_713, plain, (![A_170, B_171]: (r1_tarski(A_170, k2_relat_1(B_171)) | k10_relat_1(B_171, k1_tarski('#skF_1'(A_170, k2_relat_1(B_171))))=k1_xboole_0 | ~v1_relat_1(B_171))), inference(resolution, [status(thm)], [c_367, c_4])).
% 3.13/1.47  tff(c_500, plain, (![A_129, B_130, C_131, D_132]: (k8_relset_1(A_129, B_130, C_131, D_132)=k10_relat_1(C_131, D_132) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.13/1.47  tff(c_511, plain, (![D_132]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', D_132)=k10_relat_1('#skF_4', D_132))), inference(resolution, [status(thm)], [c_32, c_500])).
% 3.13/1.47  tff(c_48, plain, (![D_28]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', k1_tarski(D_28))!=k1_xboole_0 | ~r2_hidden(D_28, '#skF_3') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.13/1.47  tff(c_384, plain, (![D_28]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', k1_tarski(D_28))!=k1_xboole_0 | ~r2_hidden(D_28, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_70, c_48])).
% 3.13/1.47  tff(c_512, plain, (![D_28]: (k10_relat_1('#skF_4', k1_tarski(D_28))!=k1_xboole_0 | ~r2_hidden(D_28, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_511, c_384])).
% 3.13/1.47  tff(c_732, plain, (![A_170]: (~r2_hidden('#skF_1'(A_170, k2_relat_1('#skF_4')), '#skF_3') | r1_tarski(A_170, k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_713, c_512])).
% 3.13/1.47  tff(c_764, plain, (![A_174]: (~r2_hidden('#skF_1'(A_174, k2_relat_1('#skF_4')), '#skF_3') | r1_tarski(A_174, k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_732])).
% 3.13/1.47  tff(c_780, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_764])).
% 3.13/1.47  tff(c_790, plain, $false, inference(negUnitSimplification, [status(thm)], [c_463, c_463, c_780])).
% 3.13/1.47  tff(c_792, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_42])).
% 3.13/1.47  tff(c_912, plain, (![A_203, B_204, C_205]: (k2_relset_1(A_203, B_204, C_205)=k2_relat_1(C_205) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_203, B_204))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.13/1.47  tff(c_919, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_912])).
% 3.13/1.47  tff(c_922, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_792, c_919])).
% 3.13/1.47  tff(c_791, plain, (r2_hidden('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 3.13/1.47  tff(c_852, plain, (![C_189, B_190, A_191]: (r2_hidden(C_189, B_190) | ~r2_hidden(C_189, A_191) | ~r1_tarski(A_191, B_190))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.13/1.47  tff(c_858, plain, (![B_190]: (r2_hidden('#skF_5', B_190) | ~r1_tarski('#skF_3', B_190))), inference(resolution, [status(thm)], [c_791, c_852])).
% 3.13/1.47  tff(c_882, plain, (![B_197, A_198]: (k10_relat_1(B_197, k1_tarski(A_198))!=k1_xboole_0 | ~r2_hidden(A_198, k2_relat_1(B_197)) | ~v1_relat_1(B_197))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.13/1.47  tff(c_895, plain, (![B_197]: (k10_relat_1(B_197, k1_tarski('#skF_5'))!=k1_xboole_0 | ~v1_relat_1(B_197) | ~r1_tarski('#skF_3', k2_relat_1(B_197)))), inference(resolution, [status(thm)], [c_858, c_882])).
% 3.13/1.47  tff(c_926, plain, (k10_relat_1('#skF_4', k1_tarski('#skF_5'))!=k1_xboole_0 | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_922, c_895])).
% 3.13/1.47  tff(c_936, plain, (k10_relat_1('#skF_4', k1_tarski('#skF_5'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_820, c_926])).
% 3.13/1.47  tff(c_1010, plain, (![A_216, B_217, C_218, D_219]: (k8_relset_1(A_216, B_217, C_218, D_219)=k10_relat_1(C_218, D_219) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(A_216, B_217))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.13/1.47  tff(c_1022, plain, (![D_220]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', D_220)=k10_relat_1('#skF_4', D_220))), inference(resolution, [status(thm)], [c_32, c_1010])).
% 3.13/1.47  tff(c_38, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | k8_relset_1('#skF_2', '#skF_3', '#skF_4', k1_tarski('#skF_5'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.13/1.47  tff(c_793, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_38])).
% 3.13/1.47  tff(c_799, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_792, c_793])).
% 3.13/1.47  tff(c_800, plain, (k8_relset_1('#skF_2', '#skF_3', '#skF_4', k1_tarski('#skF_5'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 3.13/1.47  tff(c_1028, plain, (k10_relat_1('#skF_4', k1_tarski('#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1022, c_800])).
% 3.13/1.47  tff(c_1037, plain, $false, inference(negUnitSimplification, [status(thm)], [c_936, c_1028])).
% 3.13/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.47  
% 3.13/1.47  Inference rules
% 3.13/1.47  ----------------------
% 3.13/1.47  #Ref     : 0
% 3.13/1.47  #Sup     : 204
% 3.13/1.47  #Fact    : 0
% 3.13/1.47  #Define  : 0
% 3.13/1.47  #Split   : 11
% 3.13/1.47  #Chain   : 0
% 3.13/1.47  #Close   : 0
% 3.13/1.47  
% 3.13/1.47  Ordering : KBO
% 3.13/1.47  
% 3.13/1.47  Simplification rules
% 3.13/1.47  ----------------------
% 3.13/1.47  #Subsume      : 10
% 3.13/1.47  #Demod        : 65
% 3.13/1.47  #Tautology    : 80
% 3.13/1.47  #SimpNegUnit  : 6
% 3.13/1.47  #BackRed      : 4
% 3.13/1.47  
% 3.13/1.47  #Partial instantiations: 0
% 3.13/1.47  #Strategies tried      : 1
% 3.13/1.47  
% 3.13/1.47  Timing (in seconds)
% 3.13/1.47  ----------------------
% 3.13/1.48  Preprocessing        : 0.31
% 3.13/1.48  Parsing              : 0.16
% 3.13/1.48  CNF conversion       : 0.02
% 3.13/1.48  Main loop            : 0.40
% 3.13/1.48  Inferencing          : 0.16
% 3.13/1.48  Reduction            : 0.11
% 3.13/1.48  Demodulation         : 0.08
% 3.13/1.48  BG Simplification    : 0.02
% 3.13/1.48  Subsumption          : 0.07
% 3.13/1.48  Abstraction          : 0.02
% 3.13/1.48  MUC search           : 0.00
% 3.13/1.48  Cooper               : 0.00
% 3.13/1.48  Total                : 0.74
% 3.13/1.48  Index Insertion      : 0.00
% 3.13/1.48  Index Deletion       : 0.00
% 3.13/1.48  Index Matching       : 0.00
% 3.13/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------

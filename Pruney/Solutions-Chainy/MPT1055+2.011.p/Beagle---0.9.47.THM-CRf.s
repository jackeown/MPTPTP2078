%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:20 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 160 expanded)
%              Number of leaves         :   34 (  70 expanded)
%              Depth                    :    8
%              Number of atoms          :  142 ( 453 expanded)
%              Number of equality atoms :   21 (  44 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(A))
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(B))
                       => ( r1_tarski(k7_relset_1(A,B,C,D),E)
                        <=> r1_tarski(D,k8_relset_1(A,B,C,E)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,k7_relset_1(A,B,C,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_funct_2)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_49,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,B_57)
      | ~ m1_subset_1(A_56,k1_zfmisc_1(B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_61,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_49])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_639,plain,(
    ! [C_142,A_143,B_144] :
      ( v1_relat_1(C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_648,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_639])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_34,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_897,plain,(
    ! [A_182,B_183,C_184,D_185] :
      ( k8_relset_1(A_182,B_183,C_184,D_185) = k10_relat_1(C_184,D_185)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_904,plain,(
    ! [D_185] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_185) = k10_relat_1('#skF_3',D_185) ),
    inference(resolution,[status(thm)],[c_32,c_897])).

tff(c_824,plain,(
    ! [A_175,B_176,C_177,D_178] :
      ( k7_relset_1(A_175,B_176,C_177,D_178) = k9_relat_1(C_177,D_178)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(A_175,B_176))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_831,plain,(
    ! [D_178] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_178) = k9_relat_1('#skF_3',D_178) ),
    inference(resolution,[status(thm)],[c_32,c_824])).

tff(c_1256,plain,(
    ! [B_231,A_232,C_233] :
      ( k1_xboole_0 = B_231
      | k8_relset_1(A_232,B_231,C_233,k7_relset_1(A_232,B_231,C_233,A_232)) = A_232
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(A_232,B_231)))
      | ~ v1_funct_2(C_233,A_232,B_231)
      | ~ v1_funct_1(C_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1261,plain,
    ( k1_xboole_0 = '#skF_2'
    | k8_relset_1('#skF_1','#skF_2','#skF_3',k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1')) = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_1256])).

tff(c_1265,plain,
    ( k1_xboole_0 = '#skF_2'
    | k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_904,c_831,c_1261])).

tff(c_1266,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1265])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k10_relat_1(B_10,A_9),k1_relat_1(B_10))
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_656,plain,(
    ! [A_150,C_151,B_152] :
      ( r1_tarski(A_150,C_151)
      | ~ r1_tarski(B_152,C_151)
      | ~ r1_tarski(A_150,B_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_667,plain,(
    ! [A_150,B_10,A_9] :
      ( r1_tarski(A_150,k1_relat_1(B_10))
      | ~ r1_tarski(A_150,k10_relat_1(B_10,A_9))
      | ~ v1_relat_1(B_10) ) ),
    inference(resolution,[status(thm)],[c_12,c_656])).

tff(c_1279,plain,(
    ! [A_150] :
      ( r1_tarski(A_150,k1_relat_1('#skF_3'))
      | ~ r1_tarski(A_150,'#skF_1')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1266,c_667])).

tff(c_1324,plain,(
    ! [A_236] :
      ( r1_tarski(A_236,k1_relat_1('#skF_3'))
      | ~ r1_tarski(A_236,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_1279])).

tff(c_69,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_78,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_69])).

tff(c_241,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( k8_relset_1(A_95,B_96,C_97,D_98) = k10_relat_1(C_97,D_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_248,plain,(
    ! [D_98] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_98) = k10_relat_1('#skF_3',D_98) ),
    inference(resolution,[status(thm)],[c_32,c_241])).

tff(c_48,plain,
    ( r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5')
    | r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_62,plain,(
    r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_250,plain,(
    r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_62])).

tff(c_10,plain,(
    ! [C_8,A_6,B_7] :
      ( r1_tarski(k9_relat_1(C_8,A_6),k9_relat_1(C_8,B_7))
      | ~ r1_tarski(A_6,B_7)
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_117,plain,(
    ! [B_75,A_76] :
      ( r1_tarski(k9_relat_1(B_75,k10_relat_1(B_75,A_76)),A_76)
      | ~ v1_funct_1(B_75)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_558,plain,(
    ! [A_134,A_135,B_136] :
      ( r1_tarski(A_134,A_135)
      | ~ r1_tarski(A_134,k9_relat_1(B_136,k10_relat_1(B_136,A_135)))
      | ~ v1_funct_1(B_136)
      | ~ v1_relat_1(B_136) ) ),
    inference(resolution,[status(thm)],[c_117,c_4])).

tff(c_569,plain,(
    ! [C_137,A_138,A_139] :
      ( r1_tarski(k9_relat_1(C_137,A_138),A_139)
      | ~ v1_funct_1(C_137)
      | ~ r1_tarski(A_138,k10_relat_1(C_137,A_139))
      | ~ v1_relat_1(C_137) ) ),
    inference(resolution,[status(thm)],[c_10,c_558])).

tff(c_315,plain,(
    ! [A_102,B_103,C_104,D_105] :
      ( k7_relset_1(A_102,B_103,C_104,D_105) = k9_relat_1(C_104,D_105)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_322,plain,(
    ! [D_105] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_105) = k9_relat_1('#skF_3',D_105) ),
    inference(resolution,[status(thm)],[c_32,c_315])).

tff(c_42,plain,
    ( ~ r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_86,plain,(
    ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_42])).

tff(c_323,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_86])).

tff(c_595,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_569,c_323])).

tff(c_629,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_250,c_36,c_595])).

tff(c_630,plain,(
    r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_633,plain,(
    ~ r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_42])).

tff(c_905,plain,(
    ~ r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_904,c_633])).

tff(c_835,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_831,c_630])).

tff(c_969,plain,(
    ! [A_195,C_196,B_197] :
      ( r1_tarski(A_195,k10_relat_1(C_196,B_197))
      | ~ r1_tarski(k9_relat_1(C_196,A_195),B_197)
      | ~ r1_tarski(A_195,k1_relat_1(C_196))
      | ~ v1_funct_1(C_196)
      | ~ v1_relat_1(C_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_981,plain,
    ( r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_835,c_969])).

tff(c_1010,plain,
    ( r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_36,c_981])).

tff(c_1011,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_905,c_1010])).

tff(c_1327,plain,(
    ~ r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_1324,c_1011])).

tff(c_1341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_1327])).

tff(c_1342,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1265])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1346,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1342,c_2])).

tff(c_1348,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1346])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:56:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.69/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.67  
% 3.69/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.67  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.69/1.67  
% 3.69/1.67  %Foreground sorts:
% 3.69/1.67  
% 3.69/1.67  
% 3.69/1.67  %Background operators:
% 3.69/1.67  
% 3.69/1.67  
% 3.69/1.67  %Foreground operators:
% 3.69/1.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.69/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.69/1.67  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.69/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.69/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.69/1.67  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.69/1.67  tff('#skF_5', type, '#skF_5': $i).
% 3.69/1.67  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.69/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.69/1.67  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.69/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.69/1.67  tff('#skF_1', type, '#skF_1': $i).
% 3.69/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.69/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.69/1.67  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.69/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.69/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.69/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.69/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.69/1.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.69/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.69/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.69/1.67  
% 3.69/1.68  tff(f_111, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (r1_tarski(k7_relset_1(A, B, C, D), E) <=> r1_tarski(D, k8_relset_1(A, B, C, E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_2)).
% 3.69/1.68  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.69/1.68  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.69/1.68  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.69/1.68  tff(f_70, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.69/1.68  tff(f_86, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, k7_relset_1(A, B, C, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_funct_2)).
% 3.69/1.68  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 3.69/1.68  tff(f_32, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.69/1.68  tff(f_42, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 3.69/1.68  tff(f_52, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 3.69/1.68  tff(f_62, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 3.69/1.68  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.69/1.68  tff(c_38, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.69/1.68  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.69/1.68  tff(c_49, plain, (![A_56, B_57]: (r1_tarski(A_56, B_57) | ~m1_subset_1(A_56, k1_zfmisc_1(B_57)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.69/1.68  tff(c_61, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_49])).
% 3.69/1.68  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.69/1.69  tff(c_639, plain, (![C_142, A_143, B_144]: (v1_relat_1(C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.69/1.69  tff(c_648, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_639])).
% 3.69/1.69  tff(c_36, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.69/1.69  tff(c_34, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.69/1.69  tff(c_897, plain, (![A_182, B_183, C_184, D_185]: (k8_relset_1(A_182, B_183, C_184, D_185)=k10_relat_1(C_184, D_185) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.69/1.69  tff(c_904, plain, (![D_185]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_185)=k10_relat_1('#skF_3', D_185))), inference(resolution, [status(thm)], [c_32, c_897])).
% 3.69/1.69  tff(c_824, plain, (![A_175, B_176, C_177, D_178]: (k7_relset_1(A_175, B_176, C_177, D_178)=k9_relat_1(C_177, D_178) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.69/1.69  tff(c_831, plain, (![D_178]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_178)=k9_relat_1('#skF_3', D_178))), inference(resolution, [status(thm)], [c_32, c_824])).
% 3.69/1.69  tff(c_1256, plain, (![B_231, A_232, C_233]: (k1_xboole_0=B_231 | k8_relset_1(A_232, B_231, C_233, k7_relset_1(A_232, B_231, C_233, A_232))=A_232 | ~m1_subset_1(C_233, k1_zfmisc_1(k2_zfmisc_1(A_232, B_231))) | ~v1_funct_2(C_233, A_232, B_231) | ~v1_funct_1(C_233))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.69/1.69  tff(c_1261, plain, (k1_xboole_0='#skF_2' | k8_relset_1('#skF_1', '#skF_2', '#skF_3', k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'))='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_1256])).
% 3.69/1.69  tff(c_1265, plain, (k1_xboole_0='#skF_2' | k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_904, c_831, c_1261])).
% 3.69/1.69  tff(c_1266, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(splitLeft, [status(thm)], [c_1265])).
% 3.69/1.69  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k10_relat_1(B_10, A_9), k1_relat_1(B_10)) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.69/1.69  tff(c_656, plain, (![A_150, C_151, B_152]: (r1_tarski(A_150, C_151) | ~r1_tarski(B_152, C_151) | ~r1_tarski(A_150, B_152))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.69/1.69  tff(c_667, plain, (![A_150, B_10, A_9]: (r1_tarski(A_150, k1_relat_1(B_10)) | ~r1_tarski(A_150, k10_relat_1(B_10, A_9)) | ~v1_relat_1(B_10))), inference(resolution, [status(thm)], [c_12, c_656])).
% 3.69/1.69  tff(c_1279, plain, (![A_150]: (r1_tarski(A_150, k1_relat_1('#skF_3')) | ~r1_tarski(A_150, '#skF_1') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1266, c_667])).
% 3.69/1.69  tff(c_1324, plain, (![A_236]: (r1_tarski(A_236, k1_relat_1('#skF_3')) | ~r1_tarski(A_236, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_648, c_1279])).
% 3.69/1.69  tff(c_69, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.69/1.69  tff(c_78, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_69])).
% 3.69/1.69  tff(c_241, plain, (![A_95, B_96, C_97, D_98]: (k8_relset_1(A_95, B_96, C_97, D_98)=k10_relat_1(C_97, D_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.69/1.69  tff(c_248, plain, (![D_98]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_98)=k10_relat_1('#skF_3', D_98))), inference(resolution, [status(thm)], [c_32, c_241])).
% 3.69/1.69  tff(c_48, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5') | r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.69/1.69  tff(c_62, plain, (r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_48])).
% 3.69/1.69  tff(c_250, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_248, c_62])).
% 3.69/1.69  tff(c_10, plain, (![C_8, A_6, B_7]: (r1_tarski(k9_relat_1(C_8, A_6), k9_relat_1(C_8, B_7)) | ~r1_tarski(A_6, B_7) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.69/1.69  tff(c_117, plain, (![B_75, A_76]: (r1_tarski(k9_relat_1(B_75, k10_relat_1(B_75, A_76)), A_76) | ~v1_funct_1(B_75) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.69/1.69  tff(c_4, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.69/1.69  tff(c_558, plain, (![A_134, A_135, B_136]: (r1_tarski(A_134, A_135) | ~r1_tarski(A_134, k9_relat_1(B_136, k10_relat_1(B_136, A_135))) | ~v1_funct_1(B_136) | ~v1_relat_1(B_136))), inference(resolution, [status(thm)], [c_117, c_4])).
% 3.69/1.69  tff(c_569, plain, (![C_137, A_138, A_139]: (r1_tarski(k9_relat_1(C_137, A_138), A_139) | ~v1_funct_1(C_137) | ~r1_tarski(A_138, k10_relat_1(C_137, A_139)) | ~v1_relat_1(C_137))), inference(resolution, [status(thm)], [c_10, c_558])).
% 3.69/1.69  tff(c_315, plain, (![A_102, B_103, C_104, D_105]: (k7_relset_1(A_102, B_103, C_104, D_105)=k9_relat_1(C_104, D_105) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.69/1.69  tff(c_322, plain, (![D_105]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_105)=k9_relat_1('#skF_3', D_105))), inference(resolution, [status(thm)], [c_32, c_315])).
% 3.69/1.69  tff(c_42, plain, (~r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.69/1.69  tff(c_86, plain, (~r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_42])).
% 3.69/1.69  tff(c_323, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_322, c_86])).
% 3.69/1.69  tff(c_595, plain, (~v1_funct_1('#skF_3') | ~r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_569, c_323])).
% 3.69/1.69  tff(c_629, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_250, c_36, c_595])).
% 3.69/1.69  tff(c_630, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_48])).
% 3.69/1.69  tff(c_633, plain, (~r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_630, c_42])).
% 3.69/1.69  tff(c_905, plain, (~r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_904, c_633])).
% 3.69/1.69  tff(c_835, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_831, c_630])).
% 3.69/1.69  tff(c_969, plain, (![A_195, C_196, B_197]: (r1_tarski(A_195, k10_relat_1(C_196, B_197)) | ~r1_tarski(k9_relat_1(C_196, A_195), B_197) | ~r1_tarski(A_195, k1_relat_1(C_196)) | ~v1_funct_1(C_196) | ~v1_relat_1(C_196))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.69/1.69  tff(c_981, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_835, c_969])).
% 3.69/1.69  tff(c_1010, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_648, c_36, c_981])).
% 3.69/1.69  tff(c_1011, plain, (~r1_tarski('#skF_4', k1_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_905, c_1010])).
% 3.69/1.69  tff(c_1327, plain, (~r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_1324, c_1011])).
% 3.69/1.69  tff(c_1341, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_1327])).
% 3.69/1.69  tff(c_1342, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1265])).
% 3.69/1.69  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.69/1.69  tff(c_1346, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1342, c_2])).
% 3.69/1.69  tff(c_1348, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_1346])).
% 3.69/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.69  
% 3.69/1.69  Inference rules
% 3.69/1.69  ----------------------
% 3.69/1.69  #Ref     : 0
% 3.69/1.69  #Sup     : 317
% 3.69/1.69  #Fact    : 0
% 3.69/1.69  #Define  : 0
% 3.69/1.69  #Split   : 14
% 3.69/1.69  #Chain   : 0
% 3.69/1.69  #Close   : 0
% 3.69/1.69  
% 3.69/1.69  Ordering : KBO
% 3.69/1.69  
% 3.69/1.69  Simplification rules
% 3.69/1.69  ----------------------
% 3.69/1.69  #Subsume      : 77
% 3.69/1.69  #Demod        : 75
% 3.69/1.69  #Tautology    : 39
% 3.69/1.69  #SimpNegUnit  : 2
% 3.69/1.69  #BackRed      : 11
% 3.69/1.69  
% 3.69/1.69  #Partial instantiations: 0
% 3.69/1.69  #Strategies tried      : 1
% 3.69/1.69  
% 3.69/1.69  Timing (in seconds)
% 3.69/1.69  ----------------------
% 3.69/1.69  Preprocessing        : 0.35
% 3.69/1.69  Parsing              : 0.18
% 3.69/1.69  CNF conversion       : 0.03
% 3.69/1.69  Main loop            : 0.52
% 3.69/1.69  Inferencing          : 0.19
% 3.69/1.69  Reduction            : 0.15
% 3.69/1.69  Demodulation         : 0.10
% 3.69/1.69  BG Simplification    : 0.03
% 3.69/1.69  Subsumption          : 0.11
% 3.69/1.69  Abstraction          : 0.03
% 3.69/1.69  MUC search           : 0.00
% 3.69/1.69  Cooper               : 0.00
% 3.69/1.69  Total                : 0.91
% 3.69/1.69  Index Insertion      : 0.00
% 3.69/1.69  Index Deletion       : 0.00
% 3.69/1.69  Index Matching       : 0.00
% 3.69/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------

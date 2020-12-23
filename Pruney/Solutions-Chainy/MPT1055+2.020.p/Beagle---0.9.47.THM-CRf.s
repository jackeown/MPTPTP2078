%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:21 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 172 expanded)
%              Number of leaves         :   40 (  75 expanded)
%              Depth                    :    8
%              Number of atoms          :  161 ( 468 expanded)
%              Number of equality atoms :   22 (  39 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_2)).

tff(f_42,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_18,plain,(
    ! [A_9] : ~ v1_xboole_0(k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_87,plain,(
    ! [A_75,B_76] :
      ( r2_hidden(A_75,B_76)
      | v1_xboole_0(B_76)
      | ~ m1_subset_1(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6,plain,(
    ! [C_8,A_4] :
      ( r1_tarski(C_8,A_4)
      | ~ r2_hidden(C_8,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_91,plain,(
    ! [A_75,A_4] :
      ( r1_tarski(A_75,A_4)
      | v1_xboole_0(k1_zfmisc_1(A_4))
      | ~ m1_subset_1(A_75,k1_zfmisc_1(A_4)) ) ),
    inference(resolution,[status(thm)],[c_87,c_6])).

tff(c_611,plain,(
    ! [A_141,A_142] :
      ( r1_tarski(A_141,A_142)
      | ~ m1_subset_1(A_141,k1_zfmisc_1(A_142)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_91])).

tff(c_623,plain,(
    r1_tarski('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_611])).

tff(c_24,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_72,plain,(
    ! [B_73,A_74] :
      ( v1_relat_1(B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_74))
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_75,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_72])).

tff(c_84,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_75])).

tff(c_50,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_48,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_787,plain,(
    ! [A_171,B_172,C_173,D_174] :
      ( k8_relset_1(A_171,B_172,C_173,D_174) = k10_relat_1(C_173,D_174)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_790,plain,(
    ! [D_174] : k8_relset_1('#skF_3','#skF_4','#skF_5',D_174) = k10_relat_1('#skF_5',D_174) ),
    inference(resolution,[status(thm)],[c_46,c_787])).

tff(c_1081,plain,(
    ! [B_205,A_206,C_207] :
      ( k1_xboole_0 = B_205
      | k8_relset_1(A_206,B_205,C_207,B_205) = A_206
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_206,B_205)))
      | ~ v1_funct_2(C_207,A_206,B_205)
      | ~ v1_funct_1(C_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1083,plain,
    ( k1_xboole_0 = '#skF_4'
    | k8_relset_1('#skF_3','#skF_4','#skF_5','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_1081])).

tff(c_1086,plain,
    ( k1_xboole_0 = '#skF_4'
    | k10_relat_1('#skF_5','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_790,c_1083])).

tff(c_1087,plain,(
    k10_relat_1('#skF_5','#skF_4') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1086])).

tff(c_28,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k10_relat_1(B_21,A_20),k1_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_624,plain,(
    ! [A_143,C_144,B_145] :
      ( r1_tarski(A_143,C_144)
      | ~ r1_tarski(B_145,C_144)
      | ~ r1_tarski(A_143,B_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_639,plain,(
    ! [A_143,B_21,A_20] :
      ( r1_tarski(A_143,k1_relat_1(B_21))
      | ~ r1_tarski(A_143,k10_relat_1(B_21,A_20))
      | ~ v1_relat_1(B_21) ) ),
    inference(resolution,[status(thm)],[c_28,c_624])).

tff(c_1095,plain,(
    ! [A_143] :
      ( r1_tarski(A_143,k1_relat_1('#skF_5'))
      | ~ r1_tarski(A_143,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1087,c_639])).

tff(c_1158,plain,(
    ! [A_210] :
      ( r1_tarski(A_210,k1_relat_1('#skF_5'))
      | ~ r1_tarski(A_210,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1095])).

tff(c_306,plain,(
    ! [A_110,B_111,C_112,D_113] :
      ( k8_relset_1(A_110,B_111,C_112,D_113) = k10_relat_1(C_112,D_113)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_309,plain,(
    ! [D_113] : k8_relset_1('#skF_3','#skF_4','#skF_5',D_113) = k10_relat_1('#skF_5',D_113) ),
    inference(resolution,[status(thm)],[c_46,c_306])).

tff(c_56,plain,
    ( ~ r1_tarski('#skF_6',k8_relset_1('#skF_3','#skF_4','#skF_5','#skF_7'))
    | ~ r1_tarski(k7_relset_1('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_97,plain,(
    ~ r1_tarski(k7_relset_1('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_62,plain,
    ( r1_tarski(k7_relset_1('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7')
    | r1_tarski('#skF_6',k8_relset_1('#skF_3','#skF_4','#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_126,plain,(
    r1_tarski('#skF_6',k8_relset_1('#skF_3','#skF_4','#skF_5','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_62])).

tff(c_317,plain,(
    r1_tarski('#skF_6',k10_relat_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_126])).

tff(c_26,plain,(
    ! [C_19,A_17,B_18] :
      ( r1_tarski(k9_relat_1(C_19,A_17),k9_relat_1(C_19,B_18))
      | ~ r1_tarski(A_17,B_18)
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_138,plain,(
    ! [B_86,A_87] :
      ( r1_tarski(k9_relat_1(B_86,k10_relat_1(B_86,A_87)),A_87)
      | ~ v1_funct_1(B_86)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_549,plain,(
    ! [A_135,A_136,B_137] :
      ( r1_tarski(A_135,A_136)
      | ~ r1_tarski(A_135,k9_relat_1(B_137,k10_relat_1(B_137,A_136)))
      | ~ v1_funct_1(B_137)
      | ~ v1_relat_1(B_137) ) ),
    inference(resolution,[status(thm)],[c_138,c_4])).

tff(c_565,plain,(
    ! [C_138,A_139,A_140] :
      ( r1_tarski(k9_relat_1(C_138,A_139),A_140)
      | ~ v1_funct_1(C_138)
      | ~ r1_tarski(A_139,k10_relat_1(C_138,A_140))
      | ~ v1_relat_1(C_138) ) ),
    inference(resolution,[status(thm)],[c_26,c_549])).

tff(c_310,plain,(
    ! [A_114,B_115,C_116,D_117] :
      ( k7_relset_1(A_114,B_115,C_116,D_117) = k9_relat_1(C_116,D_117)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_313,plain,(
    ! [D_117] : k7_relset_1('#skF_3','#skF_4','#skF_5',D_117) = k9_relat_1('#skF_5',D_117) ),
    inference(resolution,[status(thm)],[c_46,c_310])).

tff(c_345,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5','#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_97])).

tff(c_579,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ r1_tarski('#skF_6',k10_relat_1('#skF_5','#skF_7'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_565,c_345])).

tff(c_603,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_317,c_50,c_579])).

tff(c_604,plain,(
    ~ r1_tarski('#skF_6',k8_relset_1('#skF_3','#skF_4','#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_791,plain,(
    ~ r1_tarski('#skF_6',k10_relat_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_604])).

tff(c_819,plain,(
    ! [A_179,B_180,C_181,D_182] :
      ( k7_relset_1(A_179,B_180,C_181,D_182) = k9_relat_1(C_181,D_182)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_822,plain,(
    ! [D_182] : k7_relset_1('#skF_3','#skF_4','#skF_5',D_182) = k9_relat_1('#skF_5',D_182) ),
    inference(resolution,[status(thm)],[c_46,c_819])).

tff(c_606,plain,(
    r1_tarski('#skF_6',k8_relset_1('#skF_3','#skF_4','#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_607,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_604,c_606])).

tff(c_608,plain,(
    r1_tarski(k7_relset_1('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_827,plain,(
    r1_tarski(k9_relat_1('#skF_5','#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_822,c_608])).

tff(c_951,plain,(
    ! [A_196,C_197,B_198] :
      ( r1_tarski(A_196,k10_relat_1(C_197,B_198))
      | ~ r1_tarski(k9_relat_1(C_197,A_196),B_198)
      | ~ r1_tarski(A_196,k1_relat_1(C_197))
      | ~ v1_funct_1(C_197)
      | ~ v1_relat_1(C_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_963,plain,
    ( r1_tarski('#skF_6',k10_relat_1('#skF_5','#skF_7'))
    | ~ r1_tarski('#skF_6',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_827,c_951])).

tff(c_991,plain,
    ( r1_tarski('#skF_6',k10_relat_1('#skF_5','#skF_7'))
    | ~ r1_tarski('#skF_6',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_50,c_963])).

tff(c_992,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_791,c_991])).

tff(c_1161,plain,(
    ~ r1_tarski('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_1158,c_992])).

tff(c_1177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_623,c_1161])).

tff(c_1178,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1086])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1182,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1178,c_2])).

tff(c_1184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1182])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:27:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.53  
% 3.42/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/1.53  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.58/1.53  
% 3.58/1.53  %Foreground sorts:
% 3.58/1.53  
% 3.58/1.53  
% 3.58/1.53  %Background operators:
% 3.58/1.53  
% 3.58/1.53  
% 3.58/1.53  %Foreground operators:
% 3.58/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.58/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.58/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.58/1.53  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.58/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.58/1.53  tff('#skF_7', type, '#skF_7': $i).
% 3.58/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.58/1.53  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.58/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.58/1.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.58/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.58/1.53  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.58/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.58/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.58/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.58/1.53  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.58/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.58/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.58/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.58/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.58/1.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.58/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.58/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.58/1.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.58/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.58/1.53  
% 3.59/1.55  tff(f_128, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (r1_tarski(k7_relset_1(A, B, C, D), E) <=> r1_tarski(D, k8_relset_1(A, B, C, E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_2)).
% 3.59/1.55  tff(f_42, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.59/1.55  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.59/1.55  tff(f_39, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.59/1.55  tff(f_57, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.59/1.55  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.59/1.55  tff(f_91, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.59/1.55  tff(f_103, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_2)).
% 3.59/1.55  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 3.59/1.55  tff(f_32, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.59/1.55  tff(f_63, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 3.59/1.55  tff(f_73, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 3.59/1.55  tff(f_87, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.59/1.55  tff(f_83, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 3.59/1.55  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.59/1.55  tff(c_52, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.59/1.55  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.59/1.55  tff(c_18, plain, (![A_9]: (~v1_xboole_0(k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.59/1.55  tff(c_87, plain, (![A_75, B_76]: (r2_hidden(A_75, B_76) | v1_xboole_0(B_76) | ~m1_subset_1(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.59/1.55  tff(c_6, plain, (![C_8, A_4]: (r1_tarski(C_8, A_4) | ~r2_hidden(C_8, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.59/1.55  tff(c_91, plain, (![A_75, A_4]: (r1_tarski(A_75, A_4) | v1_xboole_0(k1_zfmisc_1(A_4)) | ~m1_subset_1(A_75, k1_zfmisc_1(A_4)))), inference(resolution, [status(thm)], [c_87, c_6])).
% 3.59/1.55  tff(c_611, plain, (![A_141, A_142]: (r1_tarski(A_141, A_142) | ~m1_subset_1(A_141, k1_zfmisc_1(A_142)))), inference(negUnitSimplification, [status(thm)], [c_18, c_91])).
% 3.59/1.55  tff(c_623, plain, (r1_tarski('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_611])).
% 3.59/1.55  tff(c_24, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.59/1.55  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.59/1.55  tff(c_72, plain, (![B_73, A_74]: (v1_relat_1(B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_74)) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.59/1.55  tff(c_75, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_72])).
% 3.59/1.55  tff(c_84, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_75])).
% 3.59/1.55  tff(c_50, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.59/1.55  tff(c_48, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.59/1.55  tff(c_787, plain, (![A_171, B_172, C_173, D_174]: (k8_relset_1(A_171, B_172, C_173, D_174)=k10_relat_1(C_173, D_174) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.59/1.55  tff(c_790, plain, (![D_174]: (k8_relset_1('#skF_3', '#skF_4', '#skF_5', D_174)=k10_relat_1('#skF_5', D_174))), inference(resolution, [status(thm)], [c_46, c_787])).
% 3.59/1.55  tff(c_1081, plain, (![B_205, A_206, C_207]: (k1_xboole_0=B_205 | k8_relset_1(A_206, B_205, C_207, B_205)=A_206 | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_206, B_205))) | ~v1_funct_2(C_207, A_206, B_205) | ~v1_funct_1(C_207))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.59/1.55  tff(c_1083, plain, (k1_xboole_0='#skF_4' | k8_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_1081])).
% 3.59/1.55  tff(c_1086, plain, (k1_xboole_0='#skF_4' | k10_relat_1('#skF_5', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_790, c_1083])).
% 3.59/1.55  tff(c_1087, plain, (k10_relat_1('#skF_5', '#skF_4')='#skF_3'), inference(splitLeft, [status(thm)], [c_1086])).
% 3.59/1.55  tff(c_28, plain, (![B_21, A_20]: (r1_tarski(k10_relat_1(B_21, A_20), k1_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.59/1.55  tff(c_624, plain, (![A_143, C_144, B_145]: (r1_tarski(A_143, C_144) | ~r1_tarski(B_145, C_144) | ~r1_tarski(A_143, B_145))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.59/1.55  tff(c_639, plain, (![A_143, B_21, A_20]: (r1_tarski(A_143, k1_relat_1(B_21)) | ~r1_tarski(A_143, k10_relat_1(B_21, A_20)) | ~v1_relat_1(B_21))), inference(resolution, [status(thm)], [c_28, c_624])).
% 3.59/1.55  tff(c_1095, plain, (![A_143]: (r1_tarski(A_143, k1_relat_1('#skF_5')) | ~r1_tarski(A_143, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1087, c_639])).
% 3.59/1.55  tff(c_1158, plain, (![A_210]: (r1_tarski(A_210, k1_relat_1('#skF_5')) | ~r1_tarski(A_210, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1095])).
% 3.59/1.55  tff(c_306, plain, (![A_110, B_111, C_112, D_113]: (k8_relset_1(A_110, B_111, C_112, D_113)=k10_relat_1(C_112, D_113) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.59/1.55  tff(c_309, plain, (![D_113]: (k8_relset_1('#skF_3', '#skF_4', '#skF_5', D_113)=k10_relat_1('#skF_5', D_113))), inference(resolution, [status(thm)], [c_46, c_306])).
% 3.59/1.55  tff(c_56, plain, (~r1_tarski('#skF_6', k8_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')) | ~r1_tarski(k7_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.59/1.55  tff(c_97, plain, (~r1_tarski(k7_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7')), inference(splitLeft, [status(thm)], [c_56])).
% 3.59/1.55  tff(c_62, plain, (r1_tarski(k7_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7') | r1_tarski('#skF_6', k8_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.59/1.55  tff(c_126, plain, (r1_tarski('#skF_6', k8_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_97, c_62])).
% 3.59/1.55  tff(c_317, plain, (r1_tarski('#skF_6', k10_relat_1('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_126])).
% 3.59/1.55  tff(c_26, plain, (![C_19, A_17, B_18]: (r1_tarski(k9_relat_1(C_19, A_17), k9_relat_1(C_19, B_18)) | ~r1_tarski(A_17, B_18) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.59/1.55  tff(c_138, plain, (![B_86, A_87]: (r1_tarski(k9_relat_1(B_86, k10_relat_1(B_86, A_87)), A_87) | ~v1_funct_1(B_86) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.59/1.55  tff(c_4, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.59/1.55  tff(c_549, plain, (![A_135, A_136, B_137]: (r1_tarski(A_135, A_136) | ~r1_tarski(A_135, k9_relat_1(B_137, k10_relat_1(B_137, A_136))) | ~v1_funct_1(B_137) | ~v1_relat_1(B_137))), inference(resolution, [status(thm)], [c_138, c_4])).
% 3.59/1.55  tff(c_565, plain, (![C_138, A_139, A_140]: (r1_tarski(k9_relat_1(C_138, A_139), A_140) | ~v1_funct_1(C_138) | ~r1_tarski(A_139, k10_relat_1(C_138, A_140)) | ~v1_relat_1(C_138))), inference(resolution, [status(thm)], [c_26, c_549])).
% 3.59/1.55  tff(c_310, plain, (![A_114, B_115, C_116, D_117]: (k7_relset_1(A_114, B_115, C_116, D_117)=k9_relat_1(C_116, D_117) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.59/1.55  tff(c_313, plain, (![D_117]: (k7_relset_1('#skF_3', '#skF_4', '#skF_5', D_117)=k9_relat_1('#skF_5', D_117))), inference(resolution, [status(thm)], [c_46, c_310])).
% 3.59/1.55  tff(c_345, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_313, c_97])).
% 3.59/1.55  tff(c_579, plain, (~v1_funct_1('#skF_5') | ~r1_tarski('#skF_6', k10_relat_1('#skF_5', '#skF_7')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_565, c_345])).
% 3.59/1.55  tff(c_603, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_317, c_50, c_579])).
% 3.59/1.55  tff(c_604, plain, (~r1_tarski('#skF_6', k8_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_56])).
% 3.59/1.55  tff(c_791, plain, (~r1_tarski('#skF_6', k10_relat_1('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_790, c_604])).
% 3.59/1.55  tff(c_819, plain, (![A_179, B_180, C_181, D_182]: (k7_relset_1(A_179, B_180, C_181, D_182)=k9_relat_1(C_181, D_182) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.59/1.55  tff(c_822, plain, (![D_182]: (k7_relset_1('#skF_3', '#skF_4', '#skF_5', D_182)=k9_relat_1('#skF_5', D_182))), inference(resolution, [status(thm)], [c_46, c_819])).
% 3.59/1.55  tff(c_606, plain, (r1_tarski('#skF_6', k8_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'))), inference(splitLeft, [status(thm)], [c_62])).
% 3.59/1.55  tff(c_607, plain, $false, inference(negUnitSimplification, [status(thm)], [c_604, c_606])).
% 3.59/1.55  tff(c_608, plain, (r1_tarski(k7_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7')), inference(splitRight, [status(thm)], [c_62])).
% 3.59/1.55  tff(c_827, plain, (r1_tarski(k9_relat_1('#skF_5', '#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_822, c_608])).
% 3.59/1.55  tff(c_951, plain, (![A_196, C_197, B_198]: (r1_tarski(A_196, k10_relat_1(C_197, B_198)) | ~r1_tarski(k9_relat_1(C_197, A_196), B_198) | ~r1_tarski(A_196, k1_relat_1(C_197)) | ~v1_funct_1(C_197) | ~v1_relat_1(C_197))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.59/1.55  tff(c_963, plain, (r1_tarski('#skF_6', k10_relat_1('#skF_5', '#skF_7')) | ~r1_tarski('#skF_6', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_827, c_951])).
% 3.59/1.55  tff(c_991, plain, (r1_tarski('#skF_6', k10_relat_1('#skF_5', '#skF_7')) | ~r1_tarski('#skF_6', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_50, c_963])).
% 3.59/1.55  tff(c_992, plain, (~r1_tarski('#skF_6', k1_relat_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_791, c_991])).
% 3.59/1.55  tff(c_1161, plain, (~r1_tarski('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_1158, c_992])).
% 3.59/1.55  tff(c_1177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_623, c_1161])).
% 3.59/1.55  tff(c_1178, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1086])).
% 3.59/1.55  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.59/1.55  tff(c_1182, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1178, c_2])).
% 3.59/1.55  tff(c_1184, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1182])).
% 3.59/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.59/1.55  
% 3.59/1.55  Inference rules
% 3.59/1.55  ----------------------
% 3.59/1.55  #Ref     : 0
% 3.59/1.55  #Sup     : 261
% 3.59/1.55  #Fact    : 0
% 3.59/1.55  #Define  : 0
% 3.59/1.55  #Split   : 14
% 3.59/1.55  #Chain   : 0
% 3.59/1.55  #Close   : 0
% 3.59/1.55  
% 3.59/1.55  Ordering : KBO
% 3.59/1.55  
% 3.59/1.55  Simplification rules
% 3.59/1.55  ----------------------
% 3.59/1.55  #Subsume      : 54
% 3.59/1.55  #Demod        : 65
% 3.59/1.55  #Tautology    : 30
% 3.59/1.55  #SimpNegUnit  : 5
% 3.59/1.55  #BackRed      : 15
% 3.59/1.55  
% 3.59/1.55  #Partial instantiations: 0
% 3.59/1.55  #Strategies tried      : 1
% 3.59/1.55  
% 3.59/1.55  Timing (in seconds)
% 3.59/1.55  ----------------------
% 3.59/1.55  Preprocessing        : 0.33
% 3.59/1.55  Parsing              : 0.17
% 3.59/1.55  CNF conversion       : 0.03
% 3.59/1.55  Main loop            : 0.46
% 3.59/1.55  Inferencing          : 0.16
% 3.59/1.55  Reduction            : 0.14
% 3.59/1.55  Demodulation         : 0.09
% 3.59/1.55  BG Simplification    : 0.02
% 3.59/1.55  Subsumption          : 0.10
% 3.59/1.55  Abstraction          : 0.02
% 3.59/1.55  MUC search           : 0.00
% 3.59/1.55  Cooper               : 0.00
% 3.59/1.55  Total                : 0.83
% 3.59/1.55  Index Insertion      : 0.00
% 3.59/1.55  Index Deletion       : 0.00
% 3.59/1.55  Index Matching       : 0.00
% 3.59/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 10:17:19 EST 2020

% Result     : Theorem 4.03s
% Output     : CNFRefutation 4.03s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 130 expanded)
%              Number of leaves         :   35 (  60 expanded)
%              Depth                    :    6
%              Number of atoms          :  130 ( 357 expanded)
%              Number of equality atoms :   27 (  44 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_117,negated_conjecture,(
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

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_58,axiom,(
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

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_870,plain,(
    ! [A_194,B_195,C_196,D_197] :
      ( k8_relset_1(A_194,B_195,C_196,D_197) = k10_relat_1(C_196,D_197)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_194,B_195))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_877,plain,(
    ! [D_197] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_197) = k10_relat_1('#skF_3',D_197) ),
    inference(resolution,[status(thm)],[c_40,c_870])).

tff(c_76,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_85,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_76])).

tff(c_297,plain,(
    ! [A_100,B_101,C_102,D_103] :
      ( k8_relset_1(A_100,B_101,C_102,D_103) = k10_relat_1(C_102,D_103)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_304,plain,(
    ! [D_103] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_103) = k10_relat_1('#skF_3',D_103) ),
    inference(resolution,[status(thm)],[c_40,c_297])).

tff(c_50,plain,
    ( ~ r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_58,plain,(
    ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_56,plain,
    ( r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5')
    | r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_102,plain,(
    r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_56])).

tff(c_308,plain,(
    r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_102])).

tff(c_44,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_10,plain,(
    ! [C_8,A_6,B_7] :
      ( r1_tarski(k9_relat_1(C_8,A_6),k9_relat_1(C_8,B_7))
      | ~ r1_tarski(A_6,B_7)
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_141,plain,(
    ! [B_76,A_77] :
      ( r1_tarski(k9_relat_1(B_76,k10_relat_1(B_76,A_77)),A_77)
      | ~ v1_funct_1(B_76)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_436,plain,(
    ! [A_129,A_130,B_131] :
      ( r1_tarski(A_129,A_130)
      | ~ r1_tarski(A_129,k9_relat_1(B_131,k10_relat_1(B_131,A_130)))
      | ~ v1_funct_1(B_131)
      | ~ v1_relat_1(B_131) ) ),
    inference(resolution,[status(thm)],[c_141,c_4])).

tff(c_447,plain,(
    ! [C_132,A_133,A_134] :
      ( r1_tarski(k9_relat_1(C_132,A_133),A_134)
      | ~ v1_funct_1(C_132)
      | ~ r1_tarski(A_133,k10_relat_1(C_132,A_134))
      | ~ v1_relat_1(C_132) ) ),
    inference(resolution,[status(thm)],[c_10,c_436])).

tff(c_328,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( k7_relset_1(A_105,B_106,C_107,D_108) = k9_relat_1(C_107,D_108)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_335,plain,(
    ! [D_108] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_108) = k9_relat_1('#skF_3',D_108) ),
    inference(resolution,[status(thm)],[c_40,c_328])).

tff(c_336,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_58])).

tff(c_472,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_447,c_336])).

tff(c_509,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_308,c_44,c_472])).

tff(c_510,plain,(
    ~ r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_878,plain,(
    ~ r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_877,c_510])).

tff(c_529,plain,(
    ! [C_137,A_138,B_139] :
      ( v1_relat_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_538,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_529])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_512,plain,(
    ! [A_135,B_136] :
      ( r1_tarski(A_135,B_136)
      | ~ m1_subset_1(A_135,k1_zfmisc_1(B_136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_528,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_512])).

tff(c_42,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_697,plain,(
    ! [A_165,B_166,C_167] :
      ( k1_relset_1(A_165,B_166,C_167) = k1_relat_1(C_167)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_706,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_697])).

tff(c_1310,plain,(
    ! [B_256,A_257,C_258] :
      ( k1_xboole_0 = B_256
      | k1_relset_1(A_257,B_256,C_258) = A_257
      | ~ v1_funct_2(C_258,A_257,B_256)
      | ~ m1_subset_1(C_258,k1_zfmisc_1(k2_zfmisc_1(A_257,B_256))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1317,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_1310])).

tff(c_1321,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_706,c_1317])).

tff(c_1322,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1321])).

tff(c_711,plain,(
    ! [A_168,B_169,C_170,D_171] :
      ( k7_relset_1(A_168,B_169,C_170,D_171) = k9_relat_1(C_170,D_171)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_718,plain,(
    ! [D_171] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_171) = k9_relat_1('#skF_3',D_171) ),
    inference(resolution,[status(thm)],[c_40,c_711])).

tff(c_511,plain,(
    r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_722,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_718,c_511])).

tff(c_1650,plain,(
    ! [A_288,C_289,B_290] :
      ( r1_tarski(A_288,k10_relat_1(C_289,B_290))
      | ~ r1_tarski(k9_relat_1(C_289,A_288),B_290)
      | ~ r1_tarski(A_288,k1_relat_1(C_289))
      | ~ v1_funct_1(C_289)
      | ~ v1_relat_1(C_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1701,plain,
    ( r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_722,c_1650])).

tff(c_1743,plain,(
    r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_44,c_528,c_1322,c_1701])).

tff(c_1745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_878,c_1743])).

tff(c_1746,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1321])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1757,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1746,c_2])).

tff(c_1759,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1757])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:00:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.03/1.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.03/1.70  
% 4.03/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.03/1.71  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.03/1.71  
% 4.03/1.71  %Foreground sorts:
% 4.03/1.71  
% 4.03/1.71  
% 4.03/1.71  %Background operators:
% 4.03/1.71  
% 4.03/1.71  
% 4.03/1.71  %Foreground operators:
% 4.03/1.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.03/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.03/1.71  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.03/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.03/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.03/1.71  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.03/1.71  tff('#skF_5', type, '#skF_5': $i).
% 4.03/1.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.03/1.71  tff('#skF_2', type, '#skF_2': $i).
% 4.03/1.71  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.03/1.71  tff('#skF_3', type, '#skF_3': $i).
% 4.03/1.71  tff('#skF_1', type, '#skF_1': $i).
% 4.03/1.71  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.03/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.03/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.03/1.71  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.03/1.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.03/1.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.03/1.71  tff('#skF_4', type, '#skF_4': $i).
% 4.03/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.03/1.71  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.03/1.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.03/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.03/1.71  
% 4.03/1.72  tff(f_117, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (r1_tarski(k7_relset_1(A, B, C, D), E) <=> r1_tarski(D, k8_relset_1(A, B, C, E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_2)).
% 4.03/1.72  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.03/1.72  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.03/1.72  tff(f_42, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 4.03/1.72  tff(f_48, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 4.03/1.72  tff(f_32, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.03/1.72  tff(f_70, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.03/1.72  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.03/1.72  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.03/1.72  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.03/1.72  tff(f_58, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 4.03/1.72  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.03/1.72  tff(c_46, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.03/1.72  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.03/1.72  tff(c_870, plain, (![A_194, B_195, C_196, D_197]: (k8_relset_1(A_194, B_195, C_196, D_197)=k10_relat_1(C_196, D_197) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_194, B_195))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.03/1.72  tff(c_877, plain, (![D_197]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_197)=k10_relat_1('#skF_3', D_197))), inference(resolution, [status(thm)], [c_40, c_870])).
% 4.03/1.72  tff(c_76, plain, (![C_61, A_62, B_63]: (v1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.03/1.72  tff(c_85, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_76])).
% 4.03/1.72  tff(c_297, plain, (![A_100, B_101, C_102, D_103]: (k8_relset_1(A_100, B_101, C_102, D_103)=k10_relat_1(C_102, D_103) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.03/1.72  tff(c_304, plain, (![D_103]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_103)=k10_relat_1('#skF_3', D_103))), inference(resolution, [status(thm)], [c_40, c_297])).
% 4.03/1.72  tff(c_50, plain, (~r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.03/1.72  tff(c_58, plain, (~r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_50])).
% 4.03/1.72  tff(c_56, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5') | r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.03/1.72  tff(c_102, plain, (r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_58, c_56])).
% 4.03/1.72  tff(c_308, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_304, c_102])).
% 4.03/1.72  tff(c_44, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.03/1.72  tff(c_10, plain, (![C_8, A_6, B_7]: (r1_tarski(k9_relat_1(C_8, A_6), k9_relat_1(C_8, B_7)) | ~r1_tarski(A_6, B_7) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.03/1.72  tff(c_141, plain, (![B_76, A_77]: (r1_tarski(k9_relat_1(B_76, k10_relat_1(B_76, A_77)), A_77) | ~v1_funct_1(B_76) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.03/1.72  tff(c_4, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.03/1.72  tff(c_436, plain, (![A_129, A_130, B_131]: (r1_tarski(A_129, A_130) | ~r1_tarski(A_129, k9_relat_1(B_131, k10_relat_1(B_131, A_130))) | ~v1_funct_1(B_131) | ~v1_relat_1(B_131))), inference(resolution, [status(thm)], [c_141, c_4])).
% 4.03/1.72  tff(c_447, plain, (![C_132, A_133, A_134]: (r1_tarski(k9_relat_1(C_132, A_133), A_134) | ~v1_funct_1(C_132) | ~r1_tarski(A_133, k10_relat_1(C_132, A_134)) | ~v1_relat_1(C_132))), inference(resolution, [status(thm)], [c_10, c_436])).
% 4.03/1.72  tff(c_328, plain, (![A_105, B_106, C_107, D_108]: (k7_relset_1(A_105, B_106, C_107, D_108)=k9_relat_1(C_107, D_108) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.03/1.72  tff(c_335, plain, (![D_108]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_108)=k9_relat_1('#skF_3', D_108))), inference(resolution, [status(thm)], [c_40, c_328])).
% 4.03/1.72  tff(c_336, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_335, c_58])).
% 4.03/1.72  tff(c_472, plain, (~v1_funct_1('#skF_3') | ~r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_447, c_336])).
% 4.03/1.72  tff(c_509, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_308, c_44, c_472])).
% 4.03/1.72  tff(c_510, plain, (~r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_50])).
% 4.03/1.72  tff(c_878, plain, (~r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_877, c_510])).
% 4.03/1.72  tff(c_529, plain, (![C_137, A_138, B_139]: (v1_relat_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.03/1.72  tff(c_538, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_529])).
% 4.03/1.72  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.03/1.72  tff(c_512, plain, (![A_135, B_136]: (r1_tarski(A_135, B_136) | ~m1_subset_1(A_135, k1_zfmisc_1(B_136)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.03/1.72  tff(c_528, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_512])).
% 4.03/1.72  tff(c_42, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.03/1.72  tff(c_697, plain, (![A_165, B_166, C_167]: (k1_relset_1(A_165, B_166, C_167)=k1_relat_1(C_167) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.03/1.72  tff(c_706, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_697])).
% 4.03/1.72  tff(c_1310, plain, (![B_256, A_257, C_258]: (k1_xboole_0=B_256 | k1_relset_1(A_257, B_256, C_258)=A_257 | ~v1_funct_2(C_258, A_257, B_256) | ~m1_subset_1(C_258, k1_zfmisc_1(k2_zfmisc_1(A_257, B_256))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.03/1.72  tff(c_1317, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_1310])).
% 4.03/1.72  tff(c_1321, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_706, c_1317])).
% 4.03/1.72  tff(c_1322, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_1321])).
% 4.03/1.72  tff(c_711, plain, (![A_168, B_169, C_170, D_171]: (k7_relset_1(A_168, B_169, C_170, D_171)=k9_relat_1(C_170, D_171) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.03/1.72  tff(c_718, plain, (![D_171]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_171)=k9_relat_1('#skF_3', D_171))), inference(resolution, [status(thm)], [c_40, c_711])).
% 4.03/1.72  tff(c_511, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_50])).
% 4.03/1.72  tff(c_722, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_718, c_511])).
% 4.03/1.72  tff(c_1650, plain, (![A_288, C_289, B_290]: (r1_tarski(A_288, k10_relat_1(C_289, B_290)) | ~r1_tarski(k9_relat_1(C_289, A_288), B_290) | ~r1_tarski(A_288, k1_relat_1(C_289)) | ~v1_funct_1(C_289) | ~v1_relat_1(C_289))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.03/1.72  tff(c_1701, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_722, c_1650])).
% 4.03/1.72  tff(c_1743, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_538, c_44, c_528, c_1322, c_1701])).
% 4.03/1.72  tff(c_1745, plain, $false, inference(negUnitSimplification, [status(thm)], [c_878, c_1743])).
% 4.03/1.72  tff(c_1746, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1321])).
% 4.03/1.72  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.03/1.72  tff(c_1757, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1746, c_2])).
% 4.03/1.72  tff(c_1759, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_1757])).
% 4.03/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.03/1.72  
% 4.03/1.72  Inference rules
% 4.03/1.72  ----------------------
% 4.03/1.72  #Ref     : 0
% 4.03/1.72  #Sup     : 406
% 4.03/1.72  #Fact    : 0
% 4.03/1.72  #Define  : 0
% 4.03/1.72  #Split   : 15
% 4.03/1.72  #Chain   : 0
% 4.03/1.72  #Close   : 0
% 4.03/1.72  
% 4.03/1.72  Ordering : KBO
% 4.03/1.72  
% 4.03/1.72  Simplification rules
% 4.03/1.72  ----------------------
% 4.03/1.72  #Subsume      : 89
% 4.03/1.72  #Demod        : 113
% 4.03/1.72  #Tautology    : 42
% 4.03/1.72  #SimpNegUnit  : 4
% 4.03/1.72  #BackRed      : 21
% 4.03/1.72  
% 4.03/1.72  #Partial instantiations: 0
% 4.03/1.72  #Strategies tried      : 1
% 4.03/1.72  
% 4.03/1.72  Timing (in seconds)
% 4.03/1.72  ----------------------
% 4.03/1.72  Preprocessing        : 0.35
% 4.03/1.72  Parsing              : 0.18
% 4.03/1.73  CNF conversion       : 0.03
% 4.03/1.73  Main loop            : 0.60
% 4.03/1.73  Inferencing          : 0.21
% 4.03/1.73  Reduction            : 0.17
% 4.03/1.73  Demodulation         : 0.11
% 4.03/1.73  BG Simplification    : 0.03
% 4.03/1.73  Subsumption          : 0.15
% 4.03/1.73  Abstraction          : 0.03
% 4.03/1.73  MUC search           : 0.00
% 4.03/1.73  Cooper               : 0.00
% 4.03/1.73  Total                : 0.99
% 4.03/1.73  Index Insertion      : 0.00
% 4.03/1.73  Index Deletion       : 0.00
% 4.03/1.73  Index Matching       : 0.00
% 4.03/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------

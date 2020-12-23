%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:58 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 4.24s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 324 expanded)
%              Number of leaves         :   37 ( 121 expanded)
%              Depth                    :   14
%              Number of atoms          :  173 ( 559 expanded)
%              Number of equality atoms :   72 ( 252 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
          & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_90,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_46,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2159,plain,(
    ! [D_241,B_242,C_243,A_244] :
      ( m1_subset_1(D_241,k1_zfmisc_1(k2_zfmisc_1(B_242,C_243)))
      | ~ r1_tarski(k1_relat_1(D_241),B_242)
      | ~ m1_subset_1(D_241,k1_zfmisc_1(k2_zfmisc_1(A_244,C_243))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2263,plain,(
    ! [B_251] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_251,'#skF_1')))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_251) ) ),
    inference(resolution,[status(thm)],[c_44,c_2159])).

tff(c_32,plain,(
    ! [A_30,B_31,C_32,D_33] :
      ( k8_relset_1(A_30,B_31,C_32,D_33) = k10_relat_1(C_32,D_33)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2595,plain,(
    ! [B_274,D_275] :
      ( k8_relset_1(B_274,'#skF_1','#skF_3',D_275) = k10_relat_1('#skF_3',D_275)
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_274) ) ),
    inference(resolution,[status(thm)],[c_2263,c_32])).

tff(c_2617,plain,(
    ! [D_276] : k8_relset_1(k1_relat_1('#skF_3'),'#skF_1','#skF_3',D_276) = k10_relat_1('#skF_3',D_276) ),
    inference(resolution,[status(thm)],[c_6,c_2595])).

tff(c_2182,plain,(
    ! [B_242] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_242,'#skF_1')))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_242) ) ),
    inference(resolution,[status(thm)],[c_44,c_2159])).

tff(c_1542,plain,(
    ! [A_201,B_202,C_203,D_204] :
      ( m1_subset_1(k8_relset_1(A_201,B_202,C_203,D_204),k1_zfmisc_1(A_201))
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1(A_201,B_202))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2366,plain,(
    ! [A_255,B_256,C_257,D_258] :
      ( r1_tarski(k8_relset_1(A_255,B_256,C_257,D_258),A_255)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_255,B_256))) ) ),
    inference(resolution,[status(thm)],[c_1542,c_8])).

tff(c_2387,plain,(
    ! [B_242,D_258] :
      ( r1_tarski(k8_relset_1(B_242,'#skF_1','#skF_3',D_258),B_242)
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_242) ) ),
    inference(resolution,[status(thm)],[c_2182,c_2366])).

tff(c_2623,plain,(
    ! [D_276] :
      ( r1_tarski(k10_relat_1('#skF_3',D_276),k1_relat_1('#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2617,c_2387])).

tff(c_2632,plain,(
    ! [D_276] : r1_tarski(k10_relat_1('#skF_3',D_276),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2623])).

tff(c_982,plain,(
    ! [A_149,B_150,C_151] :
      ( k2_relset_1(A_149,B_150,C_151) = k2_relat_1(C_151)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_996,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_982])).

tff(c_1496,plain,(
    ! [A_194,B_195,C_196,D_197] :
      ( k7_relset_1(A_194,B_195,C_196,D_197) = k9_relat_1(C_196,D_197)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_194,B_195))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1506,plain,(
    ! [D_197] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_197) = k9_relat_1('#skF_3',D_197) ),
    inference(resolution,[status(thm)],[c_44,c_1496])).

tff(c_1867,plain,(
    ! [A_227,B_228,C_229] :
      ( k7_relset_1(A_227,B_228,C_229,A_227) = k2_relset_1(A_227,B_228,C_229)
      | ~ m1_subset_1(C_229,k1_zfmisc_1(k2_zfmisc_1(A_227,B_228))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1883,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2') = k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_1867])).

tff(c_1892,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_996,c_1506,c_1883])).

tff(c_1470,plain,(
    ! [A_189,B_190,C_191,D_192] :
      ( k8_relset_1(A_189,B_190,C_191,D_192) = k10_relat_1(C_191,D_192)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1480,plain,(
    ! [D_192] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_192) = k10_relat_1('#skF_3',D_192) ),
    inference(resolution,[status(thm)],[c_44,c_1470])).

tff(c_1194,plain,(
    ! [A_170,B_171,C_172] :
      ( k1_relset_1(A_170,B_171,C_172) = k1_relat_1(C_172)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1208,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_1194])).

tff(c_82,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_95,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_82])).

tff(c_128,plain,(
    ! [A_62,B_63] :
      ( k5_relat_1(k6_relat_1(A_62),B_63) = B_63
      | ~ r1_tarski(k1_relat_1(B_63),A_62)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_138,plain,(
    ! [B_63] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_63)),B_63) = B_63
      | ~ v1_relat_1(B_63) ) ),
    inference(resolution,[status(thm)],[c_6,c_128])).

tff(c_36,plain,(
    ! [A_38] : m1_subset_1(k6_relat_1(A_38),k1_zfmisc_1(k2_zfmisc_1(A_38,A_38))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_94,plain,(
    ! [A_38] : v1_relat_1(k6_relat_1(A_38)) ),
    inference(resolution,[status(thm)],[c_36,c_82])).

tff(c_16,plain,(
    ! [A_8] : k2_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_306,plain,(
    ! [B_87,A_88] :
      ( k9_relat_1(B_87,k2_relat_1(A_88)) = k2_relat_1(k5_relat_1(A_88,B_87))
      | ~ v1_relat_1(B_87)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_315,plain,(
    ! [A_8,B_87] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_8),B_87)) = k9_relat_1(B_87,A_8)
      | ~ v1_relat_1(B_87)
      | ~ v1_relat_1(k6_relat_1(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_306])).

tff(c_320,plain,(
    ! [A_89,B_90] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_89),B_90)) = k9_relat_1(B_90,A_89)
      | ~ v1_relat_1(B_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_315])).

tff(c_338,plain,(
    ! [B_63] :
      ( k9_relat_1(B_63,k1_relat_1(B_63)) = k2_relat_1(B_63)
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_320])).

tff(c_567,plain,(
    ! [A_101,B_102,C_103,D_104] :
      ( k8_relset_1(A_101,B_102,C_103,D_104) = k10_relat_1(C_103,D_104)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_577,plain,(
    ! [D_104] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_104) = k10_relat_1('#skF_3',D_104) ),
    inference(resolution,[status(thm)],[c_44,c_567])).

tff(c_199,plain,(
    ! [A_69,B_70,C_71] :
      ( k1_relset_1(A_69,B_70,C_71) = k1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_213,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_199])).

tff(c_786,plain,(
    ! [A_131,B_132,C_133] :
      ( k8_relset_1(A_131,B_132,C_133,B_132) = k1_relset_1(A_131,B_132,C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_799,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1') = k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_786])).

tff(c_806,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_577,c_213,c_799])).

tff(c_684,plain,(
    ! [A_121,B_122,C_123,D_124] :
      ( k7_relset_1(A_121,B_122,C_123,D_124) = k9_relat_1(C_123,D_124)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_702,plain,(
    ! [D_124] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_124) = k9_relat_1('#skF_3',D_124) ),
    inference(resolution,[status(thm)],[c_44,c_684])).

tff(c_214,plain,(
    ! [A_72,B_73,C_74] :
      ( k2_relset_1(A_72,B_73,C_74) = k2_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_228,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_214])).

tff(c_42,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_81,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_251,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_81])).

tff(c_578,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_577,c_251])).

tff(c_704,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_702,c_578])).

tff(c_871,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_806,c_704])).

tff(c_918,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_871])).

tff(c_922,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_918])).

tff(c_923,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1218,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1208,c_923])).

tff(c_1481,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1480,c_1218])).

tff(c_1507,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1506,c_1481])).

tff(c_1893,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1892,c_1507])).

tff(c_1926,plain,(
    ! [A_235,B_236,C_237] :
      ( k8_relset_1(A_235,B_236,C_237,B_236) = k1_relset_1(A_235,B_236,C_237)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_235,B_236))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1942,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1') = k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_1926])).

tff(c_1951,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1208,c_1480,c_1942])).

tff(c_1678,plain,(
    ! [A_215,B_216,C_217] :
      ( k8_relset_1(A_215,B_216,C_217,B_216) = k1_relset_1(A_215,B_216,C_217)
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1691,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1') = k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_1678])).

tff(c_1698,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1480,c_1208,c_1691])).

tff(c_925,plain,(
    ! [C_136,A_137,B_138] :
      ( v1_relat_1(C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_938,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_925])).

tff(c_1508,plain,(
    ! [D_198] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_198) = k9_relat_1('#skF_3',D_198) ),
    inference(resolution,[status(thm)],[c_44,c_1496])).

tff(c_924,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) = k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1024,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_996,c_924])).

tff(c_1482,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k10_relat_1('#skF_3','#skF_1')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1480,c_1024])).

tff(c_1514,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = k2_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1508,c_1482])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,k10_relat_1(B_12,k9_relat_1(B_12,A_11)))
      | ~ r1_tarski(A_11,k1_relat_1(B_12))
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1526,plain,
    ( r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3',k2_relat_1('#skF_3')))
    | ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1514,c_20])).

tff(c_1530,plain,
    ( r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3',k2_relat_1('#skF_3')))
    | ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_938,c_1526])).

tff(c_1592,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1530])).

tff(c_1736,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1698,c_1592])).

tff(c_1741,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1736])).

tff(c_1743,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1530])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1746,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_1743,c_2])).

tff(c_1925,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1746])).

tff(c_2014,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1951,c_1925])).

tff(c_2015,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1746])).

tff(c_1742,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3',k2_relat_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1530])).

tff(c_2017,plain,(
    r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3',k2_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2015,c_1742])).

tff(c_2121,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ r1_tarski(k10_relat_1('#skF_3',k2_relat_1('#skF_3')),k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2017,c_2])).

tff(c_2127,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k2_relat_1('#skF_3')),k1_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_1893,c_2121])).

tff(c_2636,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2632,c_2127])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:16:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.77/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.16/1.78  
% 4.16/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.16/1.78  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.16/1.78  
% 4.16/1.78  %Foreground sorts:
% 4.16/1.78  
% 4.16/1.78  
% 4.16/1.78  %Background operators:
% 4.16/1.78  
% 4.16/1.78  
% 4.16/1.78  %Foreground operators:
% 4.16/1.78  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.16/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.16/1.78  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.16/1.78  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.16/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.16/1.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.16/1.78  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.16/1.78  tff('#skF_2', type, '#skF_2': $i).
% 4.16/1.78  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.16/1.78  tff('#skF_3', type, '#skF_3': $i).
% 4.16/1.78  tff('#skF_1', type, '#skF_1': $i).
% 4.16/1.78  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.16/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.16/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.16/1.78  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.16/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.16/1.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.16/1.78  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.16/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.16/1.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.16/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.16/1.78  
% 4.24/1.80  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.24/1.80  tff(f_103, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 4.24/1.80  tff(f_88, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 4.24/1.80  tff(f_82, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.24/1.80  tff(f_66, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k8_relset_1(A, B, C, D), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 4.24/1.80  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.24/1.80  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.24/1.80  tff(f_78, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.24/1.80  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 4.24/1.80  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.24/1.80  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.24/1.80  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 4.24/1.80  tff(f_90, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 4.24/1.80  tff(f_46, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 4.24/1.80  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 4.24/1.80  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 4.24/1.80  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.24/1.80  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.24/1.80  tff(c_2159, plain, (![D_241, B_242, C_243, A_244]: (m1_subset_1(D_241, k1_zfmisc_1(k2_zfmisc_1(B_242, C_243))) | ~r1_tarski(k1_relat_1(D_241), B_242) | ~m1_subset_1(D_241, k1_zfmisc_1(k2_zfmisc_1(A_244, C_243))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.24/1.80  tff(c_2263, plain, (![B_251]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_251, '#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_3'), B_251))), inference(resolution, [status(thm)], [c_44, c_2159])).
% 4.24/1.80  tff(c_32, plain, (![A_30, B_31, C_32, D_33]: (k8_relset_1(A_30, B_31, C_32, D_33)=k10_relat_1(C_32, D_33) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.24/1.80  tff(c_2595, plain, (![B_274, D_275]: (k8_relset_1(B_274, '#skF_1', '#skF_3', D_275)=k10_relat_1('#skF_3', D_275) | ~r1_tarski(k1_relat_1('#skF_3'), B_274))), inference(resolution, [status(thm)], [c_2263, c_32])).
% 4.24/1.80  tff(c_2617, plain, (![D_276]: (k8_relset_1(k1_relat_1('#skF_3'), '#skF_1', '#skF_3', D_276)=k10_relat_1('#skF_3', D_276))), inference(resolution, [status(thm)], [c_6, c_2595])).
% 4.24/1.80  tff(c_2182, plain, (![B_242]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_242, '#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_3'), B_242))), inference(resolution, [status(thm)], [c_44, c_2159])).
% 4.24/1.80  tff(c_1542, plain, (![A_201, B_202, C_203, D_204]: (m1_subset_1(k8_relset_1(A_201, B_202, C_203, D_204), k1_zfmisc_1(A_201)) | ~m1_subset_1(C_203, k1_zfmisc_1(k2_zfmisc_1(A_201, B_202))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.24/1.80  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.24/1.80  tff(c_2366, plain, (![A_255, B_256, C_257, D_258]: (r1_tarski(k8_relset_1(A_255, B_256, C_257, D_258), A_255) | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(A_255, B_256))))), inference(resolution, [status(thm)], [c_1542, c_8])).
% 4.24/1.80  tff(c_2387, plain, (![B_242, D_258]: (r1_tarski(k8_relset_1(B_242, '#skF_1', '#skF_3', D_258), B_242) | ~r1_tarski(k1_relat_1('#skF_3'), B_242))), inference(resolution, [status(thm)], [c_2182, c_2366])).
% 4.24/1.80  tff(c_2623, plain, (![D_276]: (r1_tarski(k10_relat_1('#skF_3', D_276), k1_relat_1('#skF_3')) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2617, c_2387])).
% 4.24/1.80  tff(c_2632, plain, (![D_276]: (r1_tarski(k10_relat_1('#skF_3', D_276), k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2623])).
% 4.24/1.80  tff(c_982, plain, (![A_149, B_150, C_151]: (k2_relset_1(A_149, B_150, C_151)=k2_relat_1(C_151) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.24/1.80  tff(c_996, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_982])).
% 4.24/1.80  tff(c_1496, plain, (![A_194, B_195, C_196, D_197]: (k7_relset_1(A_194, B_195, C_196, D_197)=k9_relat_1(C_196, D_197) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_194, B_195))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.24/1.80  tff(c_1506, plain, (![D_197]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_197)=k9_relat_1('#skF_3', D_197))), inference(resolution, [status(thm)], [c_44, c_1496])).
% 4.24/1.80  tff(c_1867, plain, (![A_227, B_228, C_229]: (k7_relset_1(A_227, B_228, C_229, A_227)=k2_relset_1(A_227, B_228, C_229) | ~m1_subset_1(C_229, k1_zfmisc_1(k2_zfmisc_1(A_227, B_228))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.24/1.80  tff(c_1883, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2')=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_1867])).
% 4.24/1.80  tff(c_1892, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_996, c_1506, c_1883])).
% 4.24/1.80  tff(c_1470, plain, (![A_189, B_190, C_191, D_192]: (k8_relset_1(A_189, B_190, C_191, D_192)=k10_relat_1(C_191, D_192) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.24/1.80  tff(c_1480, plain, (![D_192]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_192)=k10_relat_1('#skF_3', D_192))), inference(resolution, [status(thm)], [c_44, c_1470])).
% 4.24/1.80  tff(c_1194, plain, (![A_170, B_171, C_172]: (k1_relset_1(A_170, B_171, C_172)=k1_relat_1(C_172) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.24/1.80  tff(c_1208, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_1194])).
% 4.24/1.80  tff(c_82, plain, (![C_51, A_52, B_53]: (v1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.24/1.80  tff(c_95, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_82])).
% 4.24/1.80  tff(c_128, plain, (![A_62, B_63]: (k5_relat_1(k6_relat_1(A_62), B_63)=B_63 | ~r1_tarski(k1_relat_1(B_63), A_62) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.24/1.80  tff(c_138, plain, (![B_63]: (k5_relat_1(k6_relat_1(k1_relat_1(B_63)), B_63)=B_63 | ~v1_relat_1(B_63))), inference(resolution, [status(thm)], [c_6, c_128])).
% 4.24/1.80  tff(c_36, plain, (![A_38]: (m1_subset_1(k6_relat_1(A_38), k1_zfmisc_1(k2_zfmisc_1(A_38, A_38))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.24/1.80  tff(c_94, plain, (![A_38]: (v1_relat_1(k6_relat_1(A_38)))), inference(resolution, [status(thm)], [c_36, c_82])).
% 4.24/1.80  tff(c_16, plain, (![A_8]: (k2_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.24/1.80  tff(c_306, plain, (![B_87, A_88]: (k9_relat_1(B_87, k2_relat_1(A_88))=k2_relat_1(k5_relat_1(A_88, B_87)) | ~v1_relat_1(B_87) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.24/1.80  tff(c_315, plain, (![A_8, B_87]: (k2_relat_1(k5_relat_1(k6_relat_1(A_8), B_87))=k9_relat_1(B_87, A_8) | ~v1_relat_1(B_87) | ~v1_relat_1(k6_relat_1(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_306])).
% 4.24/1.80  tff(c_320, plain, (![A_89, B_90]: (k2_relat_1(k5_relat_1(k6_relat_1(A_89), B_90))=k9_relat_1(B_90, A_89) | ~v1_relat_1(B_90))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_315])).
% 4.24/1.80  tff(c_338, plain, (![B_63]: (k9_relat_1(B_63, k1_relat_1(B_63))=k2_relat_1(B_63) | ~v1_relat_1(B_63) | ~v1_relat_1(B_63))), inference(superposition, [status(thm), theory('equality')], [c_138, c_320])).
% 4.24/1.80  tff(c_567, plain, (![A_101, B_102, C_103, D_104]: (k8_relset_1(A_101, B_102, C_103, D_104)=k10_relat_1(C_103, D_104) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.24/1.80  tff(c_577, plain, (![D_104]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_104)=k10_relat_1('#skF_3', D_104))), inference(resolution, [status(thm)], [c_44, c_567])).
% 4.24/1.80  tff(c_199, plain, (![A_69, B_70, C_71]: (k1_relset_1(A_69, B_70, C_71)=k1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.24/1.80  tff(c_213, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_199])).
% 4.24/1.80  tff(c_786, plain, (![A_131, B_132, C_133]: (k8_relset_1(A_131, B_132, C_133, B_132)=k1_relset_1(A_131, B_132, C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.24/1.80  tff(c_799, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1')=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_786])).
% 4.24/1.80  tff(c_806, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_577, c_213, c_799])).
% 4.24/1.80  tff(c_684, plain, (![A_121, B_122, C_123, D_124]: (k7_relset_1(A_121, B_122, C_123, D_124)=k9_relat_1(C_123, D_124) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.24/1.80  tff(c_702, plain, (![D_124]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_124)=k9_relat_1('#skF_3', D_124))), inference(resolution, [status(thm)], [c_44, c_684])).
% 4.24/1.80  tff(c_214, plain, (![A_72, B_73, C_74]: (k2_relset_1(A_72, B_73, C_74)=k2_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.24/1.80  tff(c_228, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_214])).
% 4.24/1.80  tff(c_42, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.24/1.80  tff(c_81, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_42])).
% 4.24/1.80  tff(c_251, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_228, c_81])).
% 4.24/1.80  tff(c_578, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_577, c_251])).
% 4.24/1.80  tff(c_704, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_702, c_578])).
% 4.24/1.80  tff(c_871, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_806, c_704])).
% 4.24/1.80  tff(c_918, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_338, c_871])).
% 4.24/1.80  tff(c_922, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_918])).
% 4.24/1.80  tff(c_923, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 4.24/1.80  tff(c_1218, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1208, c_923])).
% 4.24/1.80  tff(c_1481, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1480, c_1218])).
% 4.24/1.80  tff(c_1507, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1506, c_1481])).
% 4.24/1.80  tff(c_1893, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1892, c_1507])).
% 4.24/1.80  tff(c_1926, plain, (![A_235, B_236, C_237]: (k8_relset_1(A_235, B_236, C_237, B_236)=k1_relset_1(A_235, B_236, C_237) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_235, B_236))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.24/1.80  tff(c_1942, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1')=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_1926])).
% 4.24/1.80  tff(c_1951, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1208, c_1480, c_1942])).
% 4.24/1.80  tff(c_1678, plain, (![A_215, B_216, C_217]: (k8_relset_1(A_215, B_216, C_217, B_216)=k1_relset_1(A_215, B_216, C_217) | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.24/1.80  tff(c_1691, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1')=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_1678])).
% 4.24/1.80  tff(c_1698, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1480, c_1208, c_1691])).
% 4.24/1.80  tff(c_925, plain, (![C_136, A_137, B_138]: (v1_relat_1(C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.24/1.80  tff(c_938, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_925])).
% 4.24/1.80  tff(c_1508, plain, (![D_198]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_198)=k9_relat_1('#skF_3', D_198))), inference(resolution, [status(thm)], [c_44, c_1496])).
% 4.24/1.80  tff(c_924, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 4.24/1.80  tff(c_1024, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_996, c_924])).
% 4.24/1.80  tff(c_1482, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k10_relat_1('#skF_3', '#skF_1'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1480, c_1024])).
% 4.24/1.80  tff(c_1514, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))=k2_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1508, c_1482])).
% 4.24/1.80  tff(c_20, plain, (![A_11, B_12]: (r1_tarski(A_11, k10_relat_1(B_12, k9_relat_1(B_12, A_11))) | ~r1_tarski(A_11, k1_relat_1(B_12)) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.24/1.80  tff(c_1526, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', k2_relat_1('#skF_3'))) | ~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1514, c_20])).
% 4.24/1.80  tff(c_1530, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', k2_relat_1('#skF_3'))) | ~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_938, c_1526])).
% 4.24/1.80  tff(c_1592, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1530])).
% 4.24/1.80  tff(c_1736, plain, (~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1698, c_1592])).
% 4.24/1.80  tff(c_1741, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1736])).
% 4.24/1.80  tff(c_1743, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1530])).
% 4.24/1.80  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.24/1.80  tff(c_1746, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k10_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_1743, c_2])).
% 4.24/1.80  tff(c_1925, plain, (~r1_tarski(k1_relat_1('#skF_3'), k10_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_1746])).
% 4.24/1.80  tff(c_2014, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1951, c_1925])).
% 4.24/1.80  tff(c_2015, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_1746])).
% 4.24/1.80  tff(c_1742, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', k2_relat_1('#skF_3')))), inference(splitRight, [status(thm)], [c_1530])).
% 4.24/1.80  tff(c_2017, plain, (r1_tarski(k1_relat_1('#skF_3'), k10_relat_1('#skF_3', k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2015, c_1742])).
% 4.24/1.80  tff(c_2121, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3') | ~r1_tarski(k10_relat_1('#skF_3', k2_relat_1('#skF_3')), k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_2017, c_2])).
% 4.24/1.80  tff(c_2127, plain, (~r1_tarski(k10_relat_1('#skF_3', k2_relat_1('#skF_3')), k1_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1893, c_2121])).
% 4.24/1.80  tff(c_2636, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2632, c_2127])).
% 4.24/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.24/1.80  
% 4.24/1.80  Inference rules
% 4.24/1.80  ----------------------
% 4.24/1.80  #Ref     : 0
% 4.24/1.80  #Sup     : 563
% 4.24/1.80  #Fact    : 0
% 4.24/1.80  #Define  : 0
% 4.24/1.80  #Split   : 8
% 4.24/1.80  #Chain   : 0
% 4.24/1.80  #Close   : 0
% 4.24/1.80  
% 4.24/1.80  Ordering : KBO
% 4.24/1.80  
% 4.24/1.80  Simplification rules
% 4.24/1.80  ----------------------
% 4.24/1.80  #Subsume      : 15
% 4.24/1.80  #Demod        : 384
% 4.24/1.80  #Tautology    : 287
% 4.24/1.80  #SimpNegUnit  : 1
% 4.24/1.80  #BackRed      : 32
% 4.24/1.80  
% 4.24/1.80  #Partial instantiations: 0
% 4.24/1.80  #Strategies tried      : 1
% 4.24/1.80  
% 4.24/1.80  Timing (in seconds)
% 4.24/1.80  ----------------------
% 4.24/1.81  Preprocessing        : 0.34
% 4.24/1.81  Parsing              : 0.19
% 4.24/1.81  CNF conversion       : 0.02
% 4.24/1.81  Main loop            : 0.63
% 4.24/1.81  Inferencing          : 0.24
% 4.24/1.81  Reduction            : 0.20
% 4.24/1.81  Demodulation         : 0.15
% 4.24/1.81  BG Simplification    : 0.03
% 4.24/1.81  Subsumption          : 0.11
% 4.24/1.81  Abstraction          : 0.04
% 4.24/1.81  MUC search           : 0.00
% 4.24/1.81  Cooper               : 0.00
% 4.24/1.81  Total                : 1.02
% 4.24/1.81  Index Insertion      : 0.00
% 4.24/1.81  Index Deletion       : 0.00
% 4.24/1.81  Index Matching       : 0.00
% 4.24/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------

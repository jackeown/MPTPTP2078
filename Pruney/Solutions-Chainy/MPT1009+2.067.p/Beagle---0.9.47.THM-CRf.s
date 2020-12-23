%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:51 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 207 expanded)
%              Number of leaves         :   40 (  92 expanded)
%              Depth                    :   11
%              Number of atoms          :  112 ( 490 expanded)
%              Number of equality atoms :   47 ( 188 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_85,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,k1_tarski(A),B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
     => ( B != k1_xboole_0
       => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_67,plain,(
    ! [C_38,A_39,B_40] :
      ( v1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_71,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_67])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_46,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_135,plain,(
    ! [A_59,B_60,C_61] :
      ( k1_relset_1(A_59,B_60,C_61) = k1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_139,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_135])).

tff(c_162,plain,(
    ! [B_74,A_75,C_76] :
      ( k1_xboole_0 = B_74
      | k1_relset_1(A_75,B_74,C_76) = A_75
      | ~ v1_funct_2(C_76,A_75,B_74)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_75,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_165,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_162])).

tff(c_168,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_139,c_165])).

tff(c_169,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_168])).

tff(c_95,plain,(
    ! [C_49,A_50,B_51] :
      ( v4_relat_1(C_49,A_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_99,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_44,c_95])).

tff(c_100,plain,(
    ! [B_52,A_53] :
      ( k7_relat_1(B_52,A_53) = B_52
      | ~ v4_relat_1(B_52,A_53)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_103,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_99,c_100])).

tff(c_106,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_103])).

tff(c_174,plain,(
    k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_106])).

tff(c_10,plain,(
    ! [B_10,A_9] :
      ( k2_relat_1(k7_relat_1(B_10,A_9)) = k9_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_192,plain,
    ( k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_10])).

tff(c_196,plain,(
    k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_192])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k9_relat_1(B_8,A_7),k9_relat_1(B_8,k1_relat_1(B_8)))
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_206,plain,(
    ! [A_7] :
      ( r1_tarski(k9_relat_1('#skF_4',A_7),k2_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_8])).

tff(c_212,plain,(
    ! [A_7] : r1_tarski(k9_relat_1('#skF_4',A_7),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_206])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_177,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_46])).

tff(c_126,plain,(
    ! [A_56,B_57,C_58] :
      ( k2_relset_1(A_56,B_57,C_58) = k2_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_130,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_126])).

tff(c_172,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_130])).

tff(c_176,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_44])).

tff(c_263,plain,(
    ! [A_81,B_82,C_83] :
      ( k2_relset_1(k1_tarski(A_81),B_82,C_83) = k1_tarski(k1_funct_1(C_83,A_81))
      | k1_xboole_0 = B_82
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_81),B_82)))
      | ~ v1_funct_2(C_83,k1_tarski(A_81),B_82)
      | ~ v1_funct_1(C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_266,plain,(
    ! [B_82,C_83] :
      ( k2_relset_1(k1_tarski('#skF_1'),B_82,C_83) = k1_tarski(k1_funct_1(C_83,'#skF_1'))
      | k1_xboole_0 = B_82
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),B_82)))
      | ~ v1_funct_2(C_83,k1_tarski('#skF_1'),B_82)
      | ~ v1_funct_1(C_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_263])).

tff(c_285,plain,(
    ! [B_85,C_86] :
      ( k2_relset_1(k1_relat_1('#skF_4'),B_85,C_86) = k1_tarski(k1_funct_1(C_86,'#skF_1'))
      | k1_xboole_0 = B_85
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),B_85)))
      | ~ v1_funct_2(C_86,k1_relat_1('#skF_4'),B_85)
      | ~ v1_funct_1(C_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_169,c_266])).

tff(c_288,plain,
    ( k2_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4') = k1_tarski(k1_funct_1('#skF_4','#skF_1'))
    | k1_xboole_0 = '#skF_2'
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_176,c_285])).

tff(c_291,plain,
    ( k1_tarski(k1_funct_1('#skF_4','#skF_1')) = k2_relat_1('#skF_4')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_177,c_172,c_288])).

tff(c_292,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_1')) = k2_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_291])).

tff(c_145,plain,(
    ! [A_63,B_64,C_65,D_66] :
      ( k7_relset_1(A_63,B_64,C_65,D_66) = k9_relat_1(C_65,D_66)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_148,plain,(
    ! [D_66] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_66) = k9_relat_1('#skF_4',D_66) ),
    inference(resolution,[status(thm)],[c_44,c_145])).

tff(c_40,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_149,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_40])).

tff(c_293,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_149])).

tff(c_296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_293])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:40:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.27  
% 2.24/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.27  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.24/1.27  
% 2.24/1.27  %Foreground sorts:
% 2.24/1.27  
% 2.24/1.27  
% 2.24/1.27  %Background operators:
% 2.24/1.27  
% 2.24/1.27  
% 2.24/1.27  %Foreground operators:
% 2.24/1.27  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.24/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.24/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.24/1.27  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.24/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.24/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.24/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.24/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.24/1.27  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.24/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.24/1.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.24/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.24/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.27  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.24/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.24/1.27  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.24/1.27  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.24/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.24/1.27  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.24/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.24/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.24/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.24/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.24/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.24/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.27  
% 2.24/1.29  tff(f_108, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 2.24/1.29  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.24/1.29  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.24/1.29  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.24/1.29  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.24/1.29  tff(f_45, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.24/1.29  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.24/1.29  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k9_relat_1(B, k1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_relat_1)).
% 2.24/1.29  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.24/1.29  tff(f_96, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 2.24/1.29  tff(f_67, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.24/1.29  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.24/1.29  tff(c_67, plain, (![C_38, A_39, B_40]: (v1_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.24/1.29  tff(c_71, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_67])).
% 2.24/1.29  tff(c_42, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.24/1.29  tff(c_46, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.24/1.29  tff(c_135, plain, (![A_59, B_60, C_61]: (k1_relset_1(A_59, B_60, C_61)=k1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.24/1.29  tff(c_139, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_135])).
% 2.24/1.29  tff(c_162, plain, (![B_74, A_75, C_76]: (k1_xboole_0=B_74 | k1_relset_1(A_75, B_74, C_76)=A_75 | ~v1_funct_2(C_76, A_75, B_74) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_75, B_74))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.24/1.29  tff(c_165, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_44, c_162])).
% 2.24/1.29  tff(c_168, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_139, c_165])).
% 2.24/1.29  tff(c_169, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_42, c_168])).
% 2.24/1.29  tff(c_95, plain, (![C_49, A_50, B_51]: (v4_relat_1(C_49, A_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.24/1.29  tff(c_99, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_95])).
% 2.24/1.29  tff(c_100, plain, (![B_52, A_53]: (k7_relat_1(B_52, A_53)=B_52 | ~v4_relat_1(B_52, A_53) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.24/1.29  tff(c_103, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_99, c_100])).
% 2.24/1.29  tff(c_106, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_71, c_103])).
% 2.24/1.29  tff(c_174, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_169, c_106])).
% 2.24/1.29  tff(c_10, plain, (![B_10, A_9]: (k2_relat_1(k7_relat_1(B_10, A_9))=k9_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.24/1.29  tff(c_192, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_174, c_10])).
% 2.24/1.29  tff(c_196, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_192])).
% 2.24/1.29  tff(c_8, plain, (![B_8, A_7]: (r1_tarski(k9_relat_1(B_8, A_7), k9_relat_1(B_8, k1_relat_1(B_8))) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.24/1.29  tff(c_206, plain, (![A_7]: (r1_tarski(k9_relat_1('#skF_4', A_7), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_196, c_8])).
% 2.24/1.29  tff(c_212, plain, (![A_7]: (r1_tarski(k9_relat_1('#skF_4', A_7), k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_206])).
% 2.24/1.29  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.24/1.29  tff(c_177, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_46])).
% 2.24/1.29  tff(c_126, plain, (![A_56, B_57, C_58]: (k2_relset_1(A_56, B_57, C_58)=k2_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.24/1.29  tff(c_130, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_126])).
% 2.24/1.29  tff(c_172, plain, (k2_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_130])).
% 2.24/1.29  tff(c_176, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_44])).
% 2.24/1.29  tff(c_263, plain, (![A_81, B_82, C_83]: (k2_relset_1(k1_tarski(A_81), B_82, C_83)=k1_tarski(k1_funct_1(C_83, A_81)) | k1_xboole_0=B_82 | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_81), B_82))) | ~v1_funct_2(C_83, k1_tarski(A_81), B_82) | ~v1_funct_1(C_83))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.24/1.29  tff(c_266, plain, (![B_82, C_83]: (k2_relset_1(k1_tarski('#skF_1'), B_82, C_83)=k1_tarski(k1_funct_1(C_83, '#skF_1')) | k1_xboole_0=B_82 | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), B_82))) | ~v1_funct_2(C_83, k1_tarski('#skF_1'), B_82) | ~v1_funct_1(C_83))), inference(superposition, [status(thm), theory('equality')], [c_169, c_263])).
% 2.24/1.29  tff(c_285, plain, (![B_85, C_86]: (k2_relset_1(k1_relat_1('#skF_4'), B_85, C_86)=k1_tarski(k1_funct_1(C_86, '#skF_1')) | k1_xboole_0=B_85 | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), B_85))) | ~v1_funct_2(C_86, k1_relat_1('#skF_4'), B_85) | ~v1_funct_1(C_86))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_169, c_266])).
% 2.24/1.29  tff(c_288, plain, (k2_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4')=k1_tarski(k1_funct_1('#skF_4', '#skF_1')) | k1_xboole_0='#skF_2' | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_176, c_285])).
% 2.24/1.29  tff(c_291, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_1'))=k2_relat_1('#skF_4') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_177, c_172, c_288])).
% 2.24/1.29  tff(c_292, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_1'))=k2_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_42, c_291])).
% 2.24/1.29  tff(c_145, plain, (![A_63, B_64, C_65, D_66]: (k7_relset_1(A_63, B_64, C_65, D_66)=k9_relat_1(C_65, D_66) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.24/1.29  tff(c_148, plain, (![D_66]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_66)=k9_relat_1('#skF_4', D_66))), inference(resolution, [status(thm)], [c_44, c_145])).
% 2.24/1.29  tff(c_40, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.24/1.29  tff(c_149, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_40])).
% 2.24/1.29  tff(c_293, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_292, c_149])).
% 2.24/1.29  tff(c_296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_212, c_293])).
% 2.24/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.29  
% 2.24/1.29  Inference rules
% 2.24/1.29  ----------------------
% 2.24/1.29  #Ref     : 0
% 2.24/1.29  #Sup     : 55
% 2.24/1.29  #Fact    : 0
% 2.24/1.29  #Define  : 0
% 2.24/1.29  #Split   : 0
% 2.24/1.29  #Chain   : 0
% 2.24/1.29  #Close   : 0
% 2.24/1.29  
% 2.24/1.29  Ordering : KBO
% 2.24/1.29  
% 2.24/1.29  Simplification rules
% 2.24/1.29  ----------------------
% 2.24/1.29  #Subsume      : 0
% 2.24/1.29  #Demod        : 40
% 2.24/1.29  #Tautology    : 42
% 2.24/1.29  #SimpNegUnit  : 4
% 2.24/1.29  #BackRed      : 11
% 2.24/1.29  
% 2.24/1.29  #Partial instantiations: 0
% 2.24/1.29  #Strategies tried      : 1
% 2.24/1.29  
% 2.24/1.29  Timing (in seconds)
% 2.24/1.29  ----------------------
% 2.24/1.29  Preprocessing        : 0.32
% 2.24/1.29  Parsing              : 0.17
% 2.24/1.29  CNF conversion       : 0.02
% 2.24/1.29  Main loop            : 0.19
% 2.24/1.29  Inferencing          : 0.07
% 2.24/1.29  Reduction            : 0.06
% 2.24/1.29  Demodulation         : 0.05
% 2.24/1.29  BG Simplification    : 0.02
% 2.24/1.29  Subsumption          : 0.03
% 2.24/1.29  Abstraction          : 0.01
% 2.24/1.29  MUC search           : 0.00
% 2.24/1.29  Cooper               : 0.00
% 2.24/1.29  Total                : 0.55
% 2.24/1.29  Index Insertion      : 0.00
% 2.24/1.29  Index Deletion       : 0.00
% 2.24/1.29  Index Matching       : 0.00
% 2.24/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:00 EST 2020

% Result     : Theorem 4.49s
% Output     : CNFRefutation 4.64s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 203 expanded)
%              Number of leaves         :   43 (  89 expanded)
%              Depth                    :   11
%              Number of atoms          :  188 ( 624 expanded)
%              Number of equality atoms :   64 ( 193 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,B,C)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ( ( k2_relset_1(A,C,k1_partfun1(A,B,B,C,D,E)) = C
                & v2_funct_1(E) )
             => ( C = k1_xboole_0
                | k2_relset_1(A,B,D) = B ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_funct_2)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_107,axiom,(
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

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_117,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_79,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_154,plain,(
    ! [A_69,B_70,C_71] :
      ( k2_relset_1(A_69,B_70,C_71) = k2_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_166,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_154])).

tff(c_44,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_173,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_44])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_78,plain,(
    ! [B_57,A_58] :
      ( v1_relat_1(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58))
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_84,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_78])).

tff(c_91,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_84])).

tff(c_182,plain,(
    ! [A_73,B_74,C_75] :
      ( m1_subset_1(k2_relset_1(A_73,B_74,C_75),k1_zfmisc_1(B_74))
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_202,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_182])).

tff(c_213,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_202])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_233,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_213,c_2])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_54,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_121,plain,(
    ! [A_63,B_64,C_65] :
      ( k1_relset_1(A_63,B_64,C_65) = k1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_134,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_121])).

tff(c_1866,plain,(
    ! [B_241,A_242,C_243] :
      ( k1_xboole_0 = B_241
      | k1_relset_1(A_242,B_241,C_243) = A_242
      | ~ v1_funct_2(C_243,A_242,B_241)
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(A_242,B_241))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1883,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_1866])).

tff(c_1894,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_134,c_1883])).

tff(c_1895,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1894])).

tff(c_1455,plain,(
    ! [A_187,B_188,C_189,D_190] :
      ( k8_relset_1(A_187,B_188,C_189,D_190) = k10_relat_1(C_189,D_190)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1469,plain,(
    ! [D_190] : k8_relset_1('#skF_2','#skF_3','#skF_5',D_190) = k10_relat_1('#skF_5',D_190) ),
    inference(resolution,[status(thm)],[c_52,c_1455])).

tff(c_1676,plain,(
    ! [A_215,B_216,C_217] :
      ( k8_relset_1(A_215,B_216,C_217,B_216) = k1_relset_1(A_215,B_216,C_217)
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1688,plain,(
    k8_relset_1('#skF_2','#skF_3','#skF_5','#skF_3') = k1_relset_1('#skF_2','#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_1676])).

tff(c_1696,plain,(
    k10_relat_1('#skF_5','#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1469,c_134,c_1688])).

tff(c_1896,plain,(
    k10_relat_1('#skF_5','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1895,c_1696])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2292,plain,(
    ! [A_269,F_265,C_267,E_264,D_266,B_268] :
      ( k1_partfun1(A_269,B_268,C_267,D_266,E_264,F_265) = k5_relat_1(E_264,F_265)
      | ~ m1_subset_1(F_265,k1_zfmisc_1(k2_zfmisc_1(C_267,D_266)))
      | ~ v1_funct_1(F_265)
      | ~ m1_subset_1(E_264,k1_zfmisc_1(k2_zfmisc_1(A_269,B_268)))
      | ~ v1_funct_1(E_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2310,plain,(
    ! [A_269,B_268,E_264] :
      ( k1_partfun1(A_269,B_268,'#skF_2','#skF_3',E_264,'#skF_5') = k5_relat_1(E_264,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_264,k1_zfmisc_1(k2_zfmisc_1(A_269,B_268)))
      | ~ v1_funct_1(E_264) ) ),
    inference(resolution,[status(thm)],[c_52,c_2292])).

tff(c_2619,plain,(
    ! [A_273,B_274,E_275] :
      ( k1_partfun1(A_273,B_274,'#skF_2','#skF_3',E_275,'#skF_5') = k5_relat_1(E_275,'#skF_5')
      | ~ m1_subset_1(E_275,k1_zfmisc_1(k2_zfmisc_1(A_273,B_274)))
      | ~ v1_funct_1(E_275) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2310])).

tff(c_2648,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_2619])).

tff(c_2662,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2648])).

tff(c_50,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_725,plain,(
    ! [B_150,F_146,D_151,A_148,E_147,C_149] :
      ( k4_relset_1(A_148,B_150,C_149,D_151,E_147,F_146) = k5_relat_1(E_147,F_146)
      | ~ m1_subset_1(F_146,k1_zfmisc_1(k2_zfmisc_1(C_149,D_151)))
      | ~ m1_subset_1(E_147,k1_zfmisc_1(k2_zfmisc_1(A_148,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_767,plain,(
    ! [A_155,B_156,E_157] :
      ( k4_relset_1(A_155,B_156,'#skF_2','#skF_3',E_157,'#skF_5') = k5_relat_1(E_157,'#skF_5')
      | ~ m1_subset_1(E_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(resolution,[status(thm)],[c_52,c_725])).

tff(c_784,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_767])).

tff(c_837,plain,(
    ! [D_172,A_171,E_170,C_173,F_168,B_169] :
      ( m1_subset_1(k4_relset_1(A_171,B_169,C_173,D_172,E_170,F_168),k1_zfmisc_1(k2_zfmisc_1(A_171,D_172)))
      | ~ m1_subset_1(F_168,k1_zfmisc_1(k2_zfmisc_1(C_173,D_172)))
      | ~ m1_subset_1(E_170,k1_zfmisc_1(k2_zfmisc_1(A_171,B_169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_892,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_784,c_837])).

tff(c_921,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_892])).

tff(c_1184,plain,(
    ! [B_178,C_177,E_174,D_176,A_179,F_175] :
      ( k1_partfun1(A_179,B_178,C_177,D_176,E_174,F_175) = k5_relat_1(E_174,F_175)
      | ~ m1_subset_1(F_175,k1_zfmisc_1(k2_zfmisc_1(C_177,D_176)))
      | ~ v1_funct_1(F_175)
      | ~ m1_subset_1(E_174,k1_zfmisc_1(k2_zfmisc_1(A_179,B_178)))
      | ~ v1_funct_1(E_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1202,plain,(
    ! [A_179,B_178,E_174] :
      ( k1_partfun1(A_179,B_178,'#skF_2','#skF_3',E_174,'#skF_5') = k5_relat_1(E_174,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_174,k1_zfmisc_1(k2_zfmisc_1(A_179,B_178)))
      | ~ v1_funct_1(E_174) ) ),
    inference(resolution,[status(thm)],[c_52,c_1184])).

tff(c_1370,plain,(
    ! [A_180,B_181,E_182] :
      ( k1_partfun1(A_180,B_181,'#skF_2','#skF_3',E_182,'#skF_5') = k5_relat_1(E_182,'#skF_5')
      | ~ m1_subset_1(E_182,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181)))
      | ~ v1_funct_1(E_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1202])).

tff(c_1396,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_1370])).

tff(c_1409,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1396])).

tff(c_205,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_182])).

tff(c_251,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_205])).

tff(c_1421,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1409,c_251])).

tff(c_1426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_921,c_1421])).

tff(c_1428,plain,(
    m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_205])).

tff(c_20,plain,(
    ! [A_25,B_26,C_27] :
      ( k2_relset_1(A_25,B_26,C_27) = k2_relat_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1511,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = k2_relat_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1428,c_20])).

tff(c_1525,plain,(
    k2_relat_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1511])).

tff(c_2672,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2662,c_1525])).

tff(c_87,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_78])).

tff(c_94,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_87])).

tff(c_10,plain,(
    ! [B_10,A_8] :
      ( k9_relat_1(B_10,k2_relat_1(A_8)) = k2_relat_1(k5_relat_1(A_8,B_10))
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_48,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_12,plain,(
    ! [B_12,A_11] :
      ( k10_relat_1(B_12,k9_relat_1(B_12,A_11)) = A_11
      | ~ v2_funct_1(B_12)
      | ~ r1_tarski(A_11,k1_relat_1(B_12))
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1900,plain,(
    ! [A_11] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',A_11)) = A_11
      | ~ v2_funct_1('#skF_5')
      | ~ r1_tarski(A_11,'#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1895,c_12])).

tff(c_1952,plain,(
    ! [A_250] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',A_250)) = A_250
      | ~ r1_tarski(A_250,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_56,c_48,c_1900])).

tff(c_1962,plain,(
    ! [A_8] :
      ( k10_relat_1('#skF_5',k2_relat_1(k5_relat_1(A_8,'#skF_5'))) = k2_relat_1(A_8)
      | ~ r1_tarski(k2_relat_1(A_8),'#skF_2')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1952])).

tff(c_1966,plain,(
    ! [A_8] :
      ( k10_relat_1('#skF_5',k2_relat_1(k5_relat_1(A_8,'#skF_5'))) = k2_relat_1(A_8)
      | ~ r1_tarski(k2_relat_1(A_8),'#skF_2')
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_1962])).

tff(c_2687,plain,
    ( k10_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_4')
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2672,c_1966])).

tff(c_2694,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_233,c_1896,c_2687])).

tff(c_2696,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_2694])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:49:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.49/1.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.53/1.80  
% 4.53/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.53/1.80  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.53/1.80  
% 4.53/1.80  %Foreground sorts:
% 4.53/1.80  
% 4.53/1.80  
% 4.53/1.80  %Background operators:
% 4.53/1.80  
% 4.53/1.80  
% 4.53/1.80  %Foreground operators:
% 4.53/1.80  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.53/1.80  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.53/1.80  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.53/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.53/1.80  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.53/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.53/1.80  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.53/1.80  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.53/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.53/1.80  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.53/1.80  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.53/1.80  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.53/1.80  tff('#skF_5', type, '#skF_5': $i).
% 4.53/1.80  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.53/1.80  tff('#skF_2', type, '#skF_2': $i).
% 4.53/1.80  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.53/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.53/1.80  tff('#skF_1', type, '#skF_1': $i).
% 4.53/1.80  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.53/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.53/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.53/1.80  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.53/1.80  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.53/1.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.53/1.80  tff('#skF_4', type, '#skF_4': $i).
% 4.53/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.53/1.80  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.53/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.53/1.80  
% 4.64/1.82  tff(f_139, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_funct_2)).
% 4.64/1.82  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.64/1.82  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.64/1.82  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.64/1.82  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 4.64/1.82  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.64/1.82  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.64/1.82  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.64/1.82  tff(f_83, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.64/1.82  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 4.64/1.82  tff(f_117, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.64/1.82  tff(f_79, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 4.64/1.82  tff(f_65, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 4.64/1.82  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 4.64/1.82  tff(f_55, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 4.64/1.82  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.64/1.82  tff(c_154, plain, (![A_69, B_70, C_71]: (k2_relset_1(A_69, B_70, C_71)=k2_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.64/1.82  tff(c_166, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_154])).
% 4.64/1.82  tff(c_44, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.64/1.82  tff(c_173, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_166, c_44])).
% 4.64/1.82  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.64/1.82  tff(c_78, plain, (![B_57, A_58]: (v1_relat_1(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.64/1.82  tff(c_84, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_78])).
% 4.64/1.82  tff(c_91, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_84])).
% 4.64/1.82  tff(c_182, plain, (![A_73, B_74, C_75]: (m1_subset_1(k2_relset_1(A_73, B_74, C_75), k1_zfmisc_1(B_74)) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.64/1.82  tff(c_202, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_166, c_182])).
% 4.64/1.82  tff(c_213, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_202])).
% 4.64/1.82  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.64/1.82  tff(c_233, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_213, c_2])).
% 4.64/1.82  tff(c_46, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.64/1.82  tff(c_54, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.64/1.82  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.64/1.82  tff(c_121, plain, (![A_63, B_64, C_65]: (k1_relset_1(A_63, B_64, C_65)=k1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.64/1.82  tff(c_134, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_121])).
% 4.64/1.82  tff(c_1866, plain, (![B_241, A_242, C_243]: (k1_xboole_0=B_241 | k1_relset_1(A_242, B_241, C_243)=A_242 | ~v1_funct_2(C_243, A_242, B_241) | ~m1_subset_1(C_243, k1_zfmisc_1(k2_zfmisc_1(A_242, B_241))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.64/1.82  tff(c_1883, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_1866])).
% 4.64/1.82  tff(c_1894, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_134, c_1883])).
% 4.64/1.82  tff(c_1895, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_46, c_1894])).
% 4.64/1.82  tff(c_1455, plain, (![A_187, B_188, C_189, D_190]: (k8_relset_1(A_187, B_188, C_189, D_190)=k10_relat_1(C_189, D_190) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.64/1.82  tff(c_1469, plain, (![D_190]: (k8_relset_1('#skF_2', '#skF_3', '#skF_5', D_190)=k10_relat_1('#skF_5', D_190))), inference(resolution, [status(thm)], [c_52, c_1455])).
% 4.64/1.82  tff(c_1676, plain, (![A_215, B_216, C_217]: (k8_relset_1(A_215, B_216, C_217, B_216)=k1_relset_1(A_215, B_216, C_217) | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.64/1.82  tff(c_1688, plain, (k8_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_3')=k1_relset_1('#skF_2', '#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_52, c_1676])).
% 4.64/1.82  tff(c_1696, plain, (k10_relat_1('#skF_5', '#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1469, c_134, c_1688])).
% 4.64/1.82  tff(c_1896, plain, (k10_relat_1('#skF_5', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1895, c_1696])).
% 4.64/1.82  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.64/1.82  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.64/1.82  tff(c_2292, plain, (![A_269, F_265, C_267, E_264, D_266, B_268]: (k1_partfun1(A_269, B_268, C_267, D_266, E_264, F_265)=k5_relat_1(E_264, F_265) | ~m1_subset_1(F_265, k1_zfmisc_1(k2_zfmisc_1(C_267, D_266))) | ~v1_funct_1(F_265) | ~m1_subset_1(E_264, k1_zfmisc_1(k2_zfmisc_1(A_269, B_268))) | ~v1_funct_1(E_264))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.64/1.82  tff(c_2310, plain, (![A_269, B_268, E_264]: (k1_partfun1(A_269, B_268, '#skF_2', '#skF_3', E_264, '#skF_5')=k5_relat_1(E_264, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_264, k1_zfmisc_1(k2_zfmisc_1(A_269, B_268))) | ~v1_funct_1(E_264))), inference(resolution, [status(thm)], [c_52, c_2292])).
% 4.64/1.82  tff(c_2619, plain, (![A_273, B_274, E_275]: (k1_partfun1(A_273, B_274, '#skF_2', '#skF_3', E_275, '#skF_5')=k5_relat_1(E_275, '#skF_5') | ~m1_subset_1(E_275, k1_zfmisc_1(k2_zfmisc_1(A_273, B_274))) | ~v1_funct_1(E_275))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2310])).
% 4.64/1.82  tff(c_2648, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_2619])).
% 4.64/1.82  tff(c_2662, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2648])).
% 4.64/1.82  tff(c_50, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.64/1.82  tff(c_725, plain, (![B_150, F_146, D_151, A_148, E_147, C_149]: (k4_relset_1(A_148, B_150, C_149, D_151, E_147, F_146)=k5_relat_1(E_147, F_146) | ~m1_subset_1(F_146, k1_zfmisc_1(k2_zfmisc_1(C_149, D_151))) | ~m1_subset_1(E_147, k1_zfmisc_1(k2_zfmisc_1(A_148, B_150))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.64/1.82  tff(c_767, plain, (![A_155, B_156, E_157]: (k4_relset_1(A_155, B_156, '#skF_2', '#skF_3', E_157, '#skF_5')=k5_relat_1(E_157, '#skF_5') | ~m1_subset_1(E_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(resolution, [status(thm)], [c_52, c_725])).
% 4.64/1.82  tff(c_784, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_58, c_767])).
% 4.64/1.82  tff(c_837, plain, (![D_172, A_171, E_170, C_173, F_168, B_169]: (m1_subset_1(k4_relset_1(A_171, B_169, C_173, D_172, E_170, F_168), k1_zfmisc_1(k2_zfmisc_1(A_171, D_172))) | ~m1_subset_1(F_168, k1_zfmisc_1(k2_zfmisc_1(C_173, D_172))) | ~m1_subset_1(E_170, k1_zfmisc_1(k2_zfmisc_1(A_171, B_169))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.64/1.82  tff(c_892, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_784, c_837])).
% 4.64/1.82  tff(c_921, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_52, c_892])).
% 4.64/1.82  tff(c_1184, plain, (![B_178, C_177, E_174, D_176, A_179, F_175]: (k1_partfun1(A_179, B_178, C_177, D_176, E_174, F_175)=k5_relat_1(E_174, F_175) | ~m1_subset_1(F_175, k1_zfmisc_1(k2_zfmisc_1(C_177, D_176))) | ~v1_funct_1(F_175) | ~m1_subset_1(E_174, k1_zfmisc_1(k2_zfmisc_1(A_179, B_178))) | ~v1_funct_1(E_174))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.64/1.82  tff(c_1202, plain, (![A_179, B_178, E_174]: (k1_partfun1(A_179, B_178, '#skF_2', '#skF_3', E_174, '#skF_5')=k5_relat_1(E_174, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_174, k1_zfmisc_1(k2_zfmisc_1(A_179, B_178))) | ~v1_funct_1(E_174))), inference(resolution, [status(thm)], [c_52, c_1184])).
% 4.64/1.82  tff(c_1370, plain, (![A_180, B_181, E_182]: (k1_partfun1(A_180, B_181, '#skF_2', '#skF_3', E_182, '#skF_5')=k5_relat_1(E_182, '#skF_5') | ~m1_subset_1(E_182, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))) | ~v1_funct_1(E_182))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1202])).
% 4.64/1.82  tff(c_1396, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_1370])).
% 4.64/1.82  tff(c_1409, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1396])).
% 4.64/1.82  tff(c_205, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_50, c_182])).
% 4.64/1.82  tff(c_251, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitLeft, [status(thm)], [c_205])).
% 4.64/1.82  tff(c_1421, plain, (~m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1409, c_251])).
% 4.64/1.82  tff(c_1426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_921, c_1421])).
% 4.64/1.82  tff(c_1428, plain, (m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_205])).
% 4.64/1.82  tff(c_20, plain, (![A_25, B_26, C_27]: (k2_relset_1(A_25, B_26, C_27)=k2_relat_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.64/1.82  tff(c_1511, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))=k2_relat_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_1428, c_20])).
% 4.64/1.82  tff(c_1525, plain, (k2_relat_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1511])).
% 4.64/1.82  tff(c_2672, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2662, c_1525])).
% 4.64/1.82  tff(c_87, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_52, c_78])).
% 4.64/1.82  tff(c_94, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_87])).
% 4.64/1.82  tff(c_10, plain, (![B_10, A_8]: (k9_relat_1(B_10, k2_relat_1(A_8))=k2_relat_1(k5_relat_1(A_8, B_10)) | ~v1_relat_1(B_10) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.64/1.82  tff(c_48, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.64/1.82  tff(c_12, plain, (![B_12, A_11]: (k10_relat_1(B_12, k9_relat_1(B_12, A_11))=A_11 | ~v2_funct_1(B_12) | ~r1_tarski(A_11, k1_relat_1(B_12)) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.64/1.82  tff(c_1900, plain, (![A_11]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_11))=A_11 | ~v2_funct_1('#skF_5') | ~r1_tarski(A_11, '#skF_2') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1895, c_12])).
% 4.64/1.82  tff(c_1952, plain, (![A_250]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_250))=A_250 | ~r1_tarski(A_250, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_56, c_48, c_1900])).
% 4.64/1.82  tff(c_1962, plain, (![A_8]: (k10_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_8, '#skF_5')))=k2_relat_1(A_8) | ~r1_tarski(k2_relat_1(A_8), '#skF_2') | ~v1_relat_1('#skF_5') | ~v1_relat_1(A_8))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1952])).
% 4.64/1.82  tff(c_1966, plain, (![A_8]: (k10_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_8, '#skF_5')))=k2_relat_1(A_8) | ~r1_tarski(k2_relat_1(A_8), '#skF_2') | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_1962])).
% 4.64/1.82  tff(c_2687, plain, (k10_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2672, c_1966])).
% 4.64/1.82  tff(c_2694, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_91, c_233, c_1896, c_2687])).
% 4.64/1.82  tff(c_2696, plain, $false, inference(negUnitSimplification, [status(thm)], [c_173, c_2694])).
% 4.64/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.64/1.82  
% 4.64/1.82  Inference rules
% 4.64/1.82  ----------------------
% 4.64/1.82  #Ref     : 0
% 4.64/1.82  #Sup     : 628
% 4.64/1.82  #Fact    : 0
% 4.64/1.82  #Define  : 0
% 4.64/1.82  #Split   : 12
% 4.64/1.82  #Chain   : 0
% 4.64/1.82  #Close   : 0
% 4.64/1.82  
% 4.64/1.82  Ordering : KBO
% 4.64/1.82  
% 4.64/1.82  Simplification rules
% 4.64/1.82  ----------------------
% 4.64/1.82  #Subsume      : 47
% 4.64/1.82  #Demod        : 233
% 4.64/1.82  #Tautology    : 167
% 4.64/1.82  #SimpNegUnit  : 33
% 4.64/1.82  #BackRed      : 24
% 4.64/1.82  
% 4.64/1.82  #Partial instantiations: 0
% 4.64/1.82  #Strategies tried      : 1
% 4.64/1.82  
% 4.64/1.82  Timing (in seconds)
% 4.64/1.82  ----------------------
% 4.64/1.82  Preprocessing        : 0.34
% 4.64/1.82  Parsing              : 0.18
% 4.64/1.82  CNF conversion       : 0.02
% 4.64/1.82  Main loop            : 0.70
% 4.64/1.82  Inferencing          : 0.24
% 4.64/1.82  Reduction            : 0.22
% 4.64/1.82  Demodulation         : 0.16
% 4.64/1.83  BG Simplification    : 0.04
% 4.64/1.83  Subsumption          : 0.11
% 4.64/1.83  Abstraction          : 0.05
% 4.64/1.83  MUC search           : 0.00
% 4.64/1.83  Cooper               : 0.00
% 4.64/1.83  Total                : 1.08
% 4.64/1.83  Index Insertion      : 0.00
% 4.64/1.83  Index Deletion       : 0.00
% 4.64/1.83  Index Matching       : 0.00
% 4.64/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:19 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 395 expanded)
%              Number of leaves         :   33 ( 148 expanded)
%              Depth                    :   15
%              Number of atoms          :  155 (1084 expanded)
%              Number of equality atoms :   35 ( 197 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v1_funct_1(B)
              & v1_funct_2(B,A,A)
              & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( ! [C] :
                  ( m1_subset_1(C,A)
                 => k3_funct_2(A,A,B,C) = C )
             => r2_funct_2(A,A,B,k6_partfun1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t201_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_98,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_114,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_82,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_91,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_82])).

tff(c_48,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_97,plain,(
    ! [C_47,A_48,B_49] :
      ( v4_relat_1(C_47,A_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_106,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_97])).

tff(c_121,plain,(
    ! [B_57,A_58] :
      ( k1_relat_1(B_57) = A_58
      | ~ v1_partfun1(B_57,A_58)
      | ~ v4_relat_1(B_57,A_58)
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_124,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ v1_partfun1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_121])).

tff(c_127,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ v1_partfun1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_124])).

tff(c_128,plain,(
    ~ v1_partfun1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_46,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_145,plain,(
    ! [C_65,A_66,B_67] :
      ( v1_partfun1(C_65,A_66)
      | ~ v1_funct_2(C_65,A_66,B_67)
      | ~ v1_funct_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67)))
      | v1_xboole_0(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_152,plain,
    ( v1_partfun1('#skF_3','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_145])).

tff(c_156,plain,
    ( v1_partfun1('#skF_3','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_152])).

tff(c_158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_128,c_156])).

tff(c_159,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_34,plain,(
    ! [A_24] : k6_relat_1(A_24) = k6_partfun1(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_12,plain,(
    ! [B_4] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_4),B_4),k1_relat_1(B_4))
      | k6_relat_1(k1_relat_1(B_4)) = B_4
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_172,plain,(
    ! [B_70] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_70),B_70),k1_relat_1(B_70))
      | k6_partfun1(k1_relat_1(B_70)) = B_70
      | ~ v1_funct_1(B_70)
      | ~ v1_relat_1(B_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_12])).

tff(c_178,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),k1_relat_1('#skF_3'))
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_172])).

tff(c_184,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_48,c_159,c_159,c_178])).

tff(c_187,plain,(
    k6_partfun1('#skF_2') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_40,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_189,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_40])).

tff(c_218,plain,(
    ! [A_73,B_74,D_75] :
      ( r2_funct_2(A_73,B_74,D_75,D_75)
      | ~ m1_subset_1(D_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74)))
      | ~ v1_funct_2(D_75,A_73,B_74)
      | ~ v1_funct_1(D_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_223,plain,
    ( r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_218])).

tff(c_227,plain,(
    r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_223])).

tff(c_229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_227])).

tff(c_231,plain,(
    k6_partfun1('#skF_2') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_10,plain,(
    ! [B_4] :
      ( k1_funct_1(B_4,'#skF_1'(k1_relat_1(B_4),B_4)) != '#skF_1'(k1_relat_1(B_4),B_4)
      | k6_relat_1(k1_relat_1(B_4)) = B_4
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_275,plain,(
    ! [B_82] :
      ( k1_funct_1(B_82,'#skF_1'(k1_relat_1(B_82),B_82)) != '#skF_1'(k1_relat_1(B_82),B_82)
      | k6_partfun1(k1_relat_1(B_82)) = B_82
      | ~ v1_funct_1(B_82)
      | ~ v1_relat_1(B_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_10])).

tff(c_278,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'(k1_relat_1('#skF_3'),'#skF_3')
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_275])).

tff(c_280,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_48,c_159,c_159,c_278])).

tff(c_281,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_231,c_280])).

tff(c_230,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( m1_subset_1(B_2,A_1)
      | ~ r2_hidden(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_234,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_230,c_2])).

tff(c_237,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_234])).

tff(c_42,plain,(
    ! [C_33] :
      ( k3_funct_2('#skF_2','#skF_2','#skF_3',C_33) = C_33
      | ~ m1_subset_1(C_33,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_244,plain,(
    k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_237,c_42])).

tff(c_282,plain,(
    ! [A_83,B_84,C_85,D_86] :
      ( k3_funct_2(A_83,B_84,C_85,D_86) = k1_funct_1(C_85,D_86)
      | ~ m1_subset_1(D_86,A_83)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ v1_funct_2(C_85,A_83,B_84)
      | ~ v1_funct_1(C_85)
      | v1_xboole_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_284,plain,(
    ! [B_84,C_85] :
      ( k3_funct_2('#skF_2',B_84,C_85,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_85,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_84)))
      | ~ v1_funct_2(C_85,'#skF_2',B_84)
      | ~ v1_funct_1(C_85)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_237,c_282])).

tff(c_316,plain,(
    ! [B_88,C_89] :
      ( k3_funct_2('#skF_2',B_88,C_89,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_89,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_88)))
      | ~ v1_funct_2(C_89,'#skF_2',B_88)
      | ~ v1_funct_1(C_89) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_284])).

tff(c_323,plain,
    ( k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_316])).

tff(c_327,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_244,c_323])).

tff(c_329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_281,c_327])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:49:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.28  
% 2.38/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.28  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.38/1.28  
% 2.38/1.28  %Foreground sorts:
% 2.38/1.28  
% 2.38/1.28  
% 2.38/1.28  %Background operators:
% 2.38/1.28  
% 2.38/1.28  
% 2.38/1.28  %Foreground operators:
% 2.38/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.38/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.38/1.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.38/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.38/1.28  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.38/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.38/1.28  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.38/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.38/1.28  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.38/1.28  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.38/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.38/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.38/1.28  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.38/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.28  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.38/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.38/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.38/1.28  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.38/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.38/1.28  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.38/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.38/1.28  
% 2.38/1.30  tff(f_132, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((![C]: (m1_subset_1(C, A) => (k3_funct_2(A, A, B, C) = C))) => r2_funct_2(A, A, B, k6_partfun1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t201_funct_2)).
% 2.38/1.30  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.38/1.30  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.38/1.30  tff(f_83, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 2.38/1.30  tff(f_75, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.38/1.30  tff(f_98, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.38/1.30  tff(f_51, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 2.38/1.30  tff(f_114, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 2.38/1.30  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.38/1.30  tff(f_96, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.38/1.30  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.38/1.30  tff(c_82, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.38/1.30  tff(c_91, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_82])).
% 2.38/1.30  tff(c_48, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.38/1.30  tff(c_50, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.38/1.30  tff(c_97, plain, (![C_47, A_48, B_49]: (v4_relat_1(C_47, A_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.38/1.30  tff(c_106, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_97])).
% 2.38/1.30  tff(c_121, plain, (![B_57, A_58]: (k1_relat_1(B_57)=A_58 | ~v1_partfun1(B_57, A_58) | ~v4_relat_1(B_57, A_58) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.38/1.30  tff(c_124, plain, (k1_relat_1('#skF_3')='#skF_2' | ~v1_partfun1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_106, c_121])).
% 2.38/1.30  tff(c_127, plain, (k1_relat_1('#skF_3')='#skF_2' | ~v1_partfun1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_124])).
% 2.38/1.30  tff(c_128, plain, (~v1_partfun1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_127])).
% 2.38/1.30  tff(c_46, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.38/1.30  tff(c_145, plain, (![C_65, A_66, B_67]: (v1_partfun1(C_65, A_66) | ~v1_funct_2(C_65, A_66, B_67) | ~v1_funct_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))) | v1_xboole_0(B_67))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.38/1.30  tff(c_152, plain, (v1_partfun1('#skF_3', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_145])).
% 2.38/1.30  tff(c_156, plain, (v1_partfun1('#skF_3', '#skF_2') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_152])).
% 2.38/1.30  tff(c_158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_128, c_156])).
% 2.38/1.30  tff(c_159, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_127])).
% 2.38/1.30  tff(c_34, plain, (![A_24]: (k6_relat_1(A_24)=k6_partfun1(A_24))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.38/1.30  tff(c_12, plain, (![B_4]: (r2_hidden('#skF_1'(k1_relat_1(B_4), B_4), k1_relat_1(B_4)) | k6_relat_1(k1_relat_1(B_4))=B_4 | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.38/1.30  tff(c_172, plain, (![B_70]: (r2_hidden('#skF_1'(k1_relat_1(B_70), B_70), k1_relat_1(B_70)) | k6_partfun1(k1_relat_1(B_70))=B_70 | ~v1_funct_1(B_70) | ~v1_relat_1(B_70))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_12])).
% 2.38/1.30  tff(c_178, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), k1_relat_1('#skF_3')) | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_159, c_172])).
% 2.38/1.30  tff(c_184, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_91, c_48, c_159, c_159, c_178])).
% 2.38/1.30  tff(c_187, plain, (k6_partfun1('#skF_2')='#skF_3'), inference(splitLeft, [status(thm)], [c_184])).
% 2.38/1.30  tff(c_40, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.38/1.30  tff(c_189, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_187, c_40])).
% 2.38/1.30  tff(c_218, plain, (![A_73, B_74, D_75]: (r2_funct_2(A_73, B_74, D_75, D_75) | ~m1_subset_1(D_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))) | ~v1_funct_2(D_75, A_73, B_74) | ~v1_funct_1(D_75))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.38/1.30  tff(c_223, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_218])).
% 2.38/1.30  tff(c_227, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_223])).
% 2.38/1.30  tff(c_229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_189, c_227])).
% 2.38/1.30  tff(c_231, plain, (k6_partfun1('#skF_2')!='#skF_3'), inference(splitRight, [status(thm)], [c_184])).
% 2.38/1.30  tff(c_10, plain, (![B_4]: (k1_funct_1(B_4, '#skF_1'(k1_relat_1(B_4), B_4))!='#skF_1'(k1_relat_1(B_4), B_4) | k6_relat_1(k1_relat_1(B_4))=B_4 | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.38/1.30  tff(c_275, plain, (![B_82]: (k1_funct_1(B_82, '#skF_1'(k1_relat_1(B_82), B_82))!='#skF_1'(k1_relat_1(B_82), B_82) | k6_partfun1(k1_relat_1(B_82))=B_82 | ~v1_funct_1(B_82) | ~v1_relat_1(B_82))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_10])).
% 2.38/1.30  tff(c_278, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'(k1_relat_1('#skF_3'), '#skF_3') | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_159, c_275])).
% 2.38/1.30  tff(c_280, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_91, c_48, c_159, c_159, c_278])).
% 2.38/1.30  tff(c_281, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_231, c_280])).
% 2.38/1.30  tff(c_230, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_184])).
% 2.38/1.30  tff(c_2, plain, (![B_2, A_1]: (m1_subset_1(B_2, A_1) | ~r2_hidden(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.38/1.30  tff(c_234, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_230, c_2])).
% 2.38/1.30  tff(c_237, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_234])).
% 2.38/1.30  tff(c_42, plain, (![C_33]: (k3_funct_2('#skF_2', '#skF_2', '#skF_3', C_33)=C_33 | ~m1_subset_1(C_33, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.38/1.30  tff(c_244, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_237, c_42])).
% 2.38/1.30  tff(c_282, plain, (![A_83, B_84, C_85, D_86]: (k3_funct_2(A_83, B_84, C_85, D_86)=k1_funct_1(C_85, D_86) | ~m1_subset_1(D_86, A_83) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~v1_funct_2(C_85, A_83, B_84) | ~v1_funct_1(C_85) | v1_xboole_0(A_83))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.38/1.30  tff(c_284, plain, (![B_84, C_85]: (k3_funct_2('#skF_2', B_84, C_85, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_85, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_84))) | ~v1_funct_2(C_85, '#skF_2', B_84) | ~v1_funct_1(C_85) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_237, c_282])).
% 2.38/1.30  tff(c_316, plain, (![B_88, C_89]: (k3_funct_2('#skF_2', B_88, C_89, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_89, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_88))) | ~v1_funct_2(C_89, '#skF_2', B_88) | ~v1_funct_1(C_89))), inference(negUnitSimplification, [status(thm)], [c_50, c_284])).
% 2.38/1.30  tff(c_323, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_316])).
% 2.38/1.30  tff(c_327, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_244, c_323])).
% 2.38/1.30  tff(c_329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_281, c_327])).
% 2.38/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.30  
% 2.38/1.30  Inference rules
% 2.38/1.30  ----------------------
% 2.38/1.30  #Ref     : 0
% 2.38/1.30  #Sup     : 51
% 2.38/1.30  #Fact    : 0
% 2.38/1.30  #Define  : 0
% 2.38/1.30  #Split   : 5
% 2.38/1.30  #Chain   : 0
% 2.38/1.30  #Close   : 0
% 2.38/1.30  
% 2.38/1.30  Ordering : KBO
% 2.38/1.30  
% 2.38/1.30  Simplification rules
% 2.38/1.30  ----------------------
% 2.38/1.30  #Subsume      : 12
% 2.38/1.30  #Demod        : 63
% 2.38/1.30  #Tautology    : 20
% 2.38/1.30  #SimpNegUnit  : 12
% 2.38/1.30  #BackRed      : 1
% 2.38/1.30  
% 2.38/1.30  #Partial instantiations: 0
% 2.38/1.30  #Strategies tried      : 1
% 2.38/1.30  
% 2.38/1.30  Timing (in seconds)
% 2.38/1.30  ----------------------
% 2.38/1.30  Preprocessing        : 0.32
% 2.38/1.30  Parsing              : 0.17
% 2.38/1.30  CNF conversion       : 0.02
% 2.38/1.30  Main loop            : 0.22
% 2.38/1.30  Inferencing          : 0.08
% 2.38/1.30  Reduction            : 0.07
% 2.38/1.30  Demodulation         : 0.05
% 2.38/1.30  BG Simplification    : 0.02
% 2.38/1.30  Subsumption          : 0.04
% 2.38/1.30  Abstraction          : 0.01
% 2.38/1.30  MUC search           : 0.00
% 2.38/1.30  Cooper               : 0.00
% 2.38/1.30  Total                : 0.57
% 2.38/1.30  Index Insertion      : 0.00
% 2.38/1.30  Index Deletion       : 0.00
% 2.38/1.30  Index Matching       : 0.00
% 2.38/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------

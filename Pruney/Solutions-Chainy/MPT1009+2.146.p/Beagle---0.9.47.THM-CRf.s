%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:02 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 156 expanded)
%              Number of leaves         :   39 (  72 expanded)
%              Depth                    :   10
%              Number of atoms          :   99 ( 304 expanded)
%              Number of equality atoms :   37 (  74 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_94,axiom,(
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

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_relat_1)).

tff(c_10,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_68,plain,(
    ! [B_38,A_39] :
      ( v1_relat_1(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_39))
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_71,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_68])).

tff(c_74,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_71])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_154,plain,(
    ! [B_66,A_67] :
      ( k1_tarski(k1_funct_1(B_66,A_67)) = k2_relat_1(B_66)
      | k1_tarski(A_67) != k1_relat_1(B_66)
      | ~ v1_funct_1(B_66)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_140,plain,(
    ! [A_61,B_62,C_63,D_64] :
      ( k7_relset_1(A_61,B_62,C_63,D_64) = k9_relat_1(C_63,D_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_143,plain,(
    ! [D_64] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_64) = k9_relat_1('#skF_4',D_64) ),
    inference(resolution,[status(thm)],[c_44,c_140])).

tff(c_40,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_144,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_40])).

tff(c_160,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_144])).

tff(c_166,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_48,c_160])).

tff(c_168,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_46,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_129,plain,(
    ! [A_55,B_56,C_57] :
      ( k1_relset_1(A_55,B_56,C_57) = k1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_133,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_129])).

tff(c_171,plain,(
    ! [B_72,A_73,C_74] :
      ( k1_xboole_0 = B_72
      | k1_relset_1(A_73,B_72,C_74) = A_73
      | ~ v1_funct_2(C_74,A_73,B_72)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_73,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_174,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_171])).

tff(c_177,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_133,c_174])).

tff(c_179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_168,c_42,c_177])).

tff(c_181,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_90,plain,(
    ! [C_47,A_48,B_49] :
      ( v4_relat_1(C_47,A_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_94,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_44,c_90])).

tff(c_16,plain,(
    ! [B_17,A_16] :
      ( k7_relat_1(B_17,A_16) = B_17
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_106,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_94,c_16])).

tff(c_109,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_106])).

tff(c_14,plain,(
    ! [B_15,A_14] :
      ( k2_relat_1(k7_relat_1(B_15,A_14)) = k9_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_113,plain,
    ( k9_relat_1('#skF_4',k1_tarski('#skF_1')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_14])).

tff(c_117,plain,(
    k9_relat_1('#skF_4',k1_tarski('#skF_1')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_113])).

tff(c_184,plain,(
    k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_117])).

tff(c_12,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k9_relat_1(B_13,A_12),k9_relat_1(B_13,k1_relat_1(B_13)))
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_240,plain,(
    ! [A_12] :
      ( r1_tarski(k9_relat_1('#skF_4',A_12),k2_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_12])).

tff(c_246,plain,(
    ! [A_12] : r1_tarski(k9_relat_1('#skF_4',A_12),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_240])).

tff(c_180,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_180])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:40:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.39  
% 2.38/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.40  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.38/1.40  
% 2.38/1.40  %Foreground sorts:
% 2.38/1.40  
% 2.38/1.40  
% 2.38/1.40  %Background operators:
% 2.38/1.40  
% 2.38/1.40  
% 2.38/1.40  %Foreground operators:
% 2.38/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.38/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.38/1.40  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.38/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.38/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.38/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.38/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.38/1.40  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.38/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.38/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.38/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.38/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.38/1.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.38/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.38/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.38/1.40  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.38/1.40  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.38/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.38/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.38/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.38/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.38/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.38/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.40  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.38/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.38/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.38/1.40  
% 2.38/1.41  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.38/1.41  tff(f_106, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 2.38/1.41  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.38/1.41  tff(f_62, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 2.38/1.41  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.38/1.41  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.38/1.41  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.38/1.41  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.38/1.41  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.38/1.41  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.38/1.41  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k9_relat_1(B, k1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_relat_1)).
% 2.38/1.41  tff(c_10, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.38/1.41  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.38/1.41  tff(c_68, plain, (![B_38, A_39]: (v1_relat_1(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_39)) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.38/1.41  tff(c_71, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_68])).
% 2.38/1.41  tff(c_74, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_71])).
% 2.38/1.41  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.38/1.41  tff(c_154, plain, (![B_66, A_67]: (k1_tarski(k1_funct_1(B_66, A_67))=k2_relat_1(B_66) | k1_tarski(A_67)!=k1_relat_1(B_66) | ~v1_funct_1(B_66) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.38/1.41  tff(c_140, plain, (![A_61, B_62, C_63, D_64]: (k7_relset_1(A_61, B_62, C_63, D_64)=k9_relat_1(C_63, D_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.38/1.41  tff(c_143, plain, (![D_64]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_64)=k9_relat_1('#skF_4', D_64))), inference(resolution, [status(thm)], [c_44, c_140])).
% 2.38/1.41  tff(c_40, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.38/1.41  tff(c_144, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_40])).
% 2.38/1.41  tff(c_160, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_154, c_144])).
% 2.38/1.41  tff(c_166, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_48, c_160])).
% 2.38/1.41  tff(c_168, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_166])).
% 2.38/1.41  tff(c_42, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.38/1.41  tff(c_46, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.38/1.41  tff(c_129, plain, (![A_55, B_56, C_57]: (k1_relset_1(A_55, B_56, C_57)=k1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.38/1.41  tff(c_133, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_129])).
% 2.38/1.41  tff(c_171, plain, (![B_72, A_73, C_74]: (k1_xboole_0=B_72 | k1_relset_1(A_73, B_72, C_74)=A_73 | ~v1_funct_2(C_74, A_73, B_72) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_73, B_72))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.38/1.41  tff(c_174, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_44, c_171])).
% 2.38/1.41  tff(c_177, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_133, c_174])).
% 2.38/1.41  tff(c_179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_168, c_42, c_177])).
% 2.38/1.41  tff(c_181, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_166])).
% 2.38/1.41  tff(c_90, plain, (![C_47, A_48, B_49]: (v4_relat_1(C_47, A_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.38/1.41  tff(c_94, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_90])).
% 2.38/1.41  tff(c_16, plain, (![B_17, A_16]: (k7_relat_1(B_17, A_16)=B_17 | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.38/1.41  tff(c_106, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_94, c_16])).
% 2.38/1.41  tff(c_109, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_106])).
% 2.38/1.41  tff(c_14, plain, (![B_15, A_14]: (k2_relat_1(k7_relat_1(B_15, A_14))=k9_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.38/1.41  tff(c_113, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_1'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_109, c_14])).
% 2.38/1.41  tff(c_117, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_1'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_113])).
% 2.38/1.41  tff(c_184, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_181, c_117])).
% 2.38/1.41  tff(c_12, plain, (![B_13, A_12]: (r1_tarski(k9_relat_1(B_13, A_12), k9_relat_1(B_13, k1_relat_1(B_13))) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.38/1.41  tff(c_240, plain, (![A_12]: (r1_tarski(k9_relat_1('#skF_4', A_12), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_184, c_12])).
% 2.38/1.41  tff(c_246, plain, (![A_12]: (r1_tarski(k9_relat_1('#skF_4', A_12), k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_240])).
% 2.38/1.41  tff(c_180, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_166])).
% 2.38/1.41  tff(c_253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_246, c_180])).
% 2.38/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.41  
% 2.38/1.41  Inference rules
% 2.38/1.41  ----------------------
% 2.38/1.41  #Ref     : 0
% 2.38/1.41  #Sup     : 43
% 2.38/1.41  #Fact    : 0
% 2.38/1.41  #Define  : 0
% 2.38/1.41  #Split   : 1
% 2.38/1.41  #Chain   : 0
% 2.38/1.41  #Close   : 0
% 2.38/1.41  
% 2.38/1.41  Ordering : KBO
% 2.38/1.41  
% 2.38/1.41  Simplification rules
% 2.38/1.41  ----------------------
% 2.38/1.41  #Subsume      : 0
% 2.38/1.41  #Demod        : 30
% 2.38/1.41  #Tautology    : 30
% 2.38/1.41  #SimpNegUnit  : 1
% 2.38/1.41  #BackRed      : 10
% 2.38/1.41  
% 2.38/1.41  #Partial instantiations: 0
% 2.38/1.41  #Strategies tried      : 1
% 2.38/1.41  
% 2.38/1.41  Timing (in seconds)
% 2.38/1.41  ----------------------
% 2.38/1.41  Preprocessing        : 0.37
% 2.38/1.41  Parsing              : 0.19
% 2.38/1.41  CNF conversion       : 0.02
% 2.38/1.41  Main loop            : 0.19
% 2.38/1.41  Inferencing          : 0.07
% 2.38/1.41  Reduction            : 0.06
% 2.38/1.41  Demodulation         : 0.04
% 2.38/1.41  BG Simplification    : 0.02
% 2.38/1.41  Subsumption          : 0.02
% 2.38/1.41  Abstraction          : 0.01
% 2.38/1.41  MUC search           : 0.00
% 2.38/1.41  Cooper               : 0.00
% 2.38/1.42  Total                : 0.59
% 2.38/1.42  Index Insertion      : 0.00
% 2.38/1.42  Index Deletion       : 0.00
% 2.38/1.42  Index Matching       : 0.00
% 2.38/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------

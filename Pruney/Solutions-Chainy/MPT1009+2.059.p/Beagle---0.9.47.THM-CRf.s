%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:50 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 151 expanded)
%              Number of leaves         :   38 (  68 expanded)
%              Depth                    :    8
%              Number of atoms          :  108 ( 290 expanded)
%              Number of equality atoms :   50 ( 101 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_102,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_48,axiom,(
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

tff(f_60,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_99,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_103,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_99])).

tff(c_24,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k9_relat_1(B_14,A_13),k2_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_30,plain,(
    ! [A_16] :
      ( k1_relat_1(A_16) != k1_xboole_0
      | k1_xboole_0 = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_116,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_103,c_30])).

tff(c_118,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_158,plain,(
    ! [B_66,A_67] :
      ( k1_tarski(k1_funct_1(B_66,A_67)) = k2_relat_1(B_66)
      | k1_tarski(A_67) != k1_relat_1(B_66)
      | ~ v1_funct_1(B_66)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_144,plain,(
    ! [A_61,B_62,C_63,D_64] :
      ( k7_relset_1(A_61,B_62,C_63,D_64) = k9_relat_1(C_63,D_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_147,plain,(
    ! [D_64] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_64) = k9_relat_1('#skF_4',D_64) ),
    inference(resolution,[status(thm)],[c_46,c_144])).

tff(c_42,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_148,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_42])).

tff(c_164,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_148])).

tff(c_182,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_50,c_164])).

tff(c_184,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_182])).

tff(c_120,plain,(
    ! [C_50,A_51,B_52] :
      ( v4_relat_1(C_50,A_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_124,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_46,c_120])).

tff(c_22,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_185,plain,(
    ! [B_68,C_69,A_70] :
      ( k2_tarski(B_68,C_69) = A_70
      | k1_tarski(C_69) = A_70
      | k1_tarski(B_68) = A_70
      | k1_xboole_0 = A_70
      | ~ r1_tarski(A_70,k2_tarski(B_68,C_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_201,plain,(
    ! [A_2,A_70] :
      ( k2_tarski(A_2,A_2) = A_70
      | k1_tarski(A_2) = A_70
      | k1_tarski(A_2) = A_70
      | k1_xboole_0 = A_70
      | ~ r1_tarski(A_70,k1_tarski(A_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_185])).

tff(c_216,plain,(
    ! [A_71,A_72] :
      ( k1_tarski(A_71) = A_72
      | k1_tarski(A_71) = A_72
      | k1_tarski(A_71) = A_72
      | k1_xboole_0 = A_72
      | ~ r1_tarski(A_72,k1_tarski(A_71)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_201])).

tff(c_236,plain,(
    ! [A_73,B_74] :
      ( k1_tarski(A_73) = k1_relat_1(B_74)
      | k1_relat_1(B_74) = k1_xboole_0
      | ~ v4_relat_1(B_74,k1_tarski(A_73))
      | ~ v1_relat_1(B_74) ) ),
    inference(resolution,[status(thm)],[c_22,c_216])).

tff(c_242,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_124,c_236])).

tff(c_245,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_242])).

tff(c_247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_184,c_245])).

tff(c_248,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_281,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_248])).

tff(c_285,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_281])).

tff(c_286,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_292,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_2])).

tff(c_26,plain,(
    ! [A_15] : k9_relat_1(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_291,plain,(
    ! [A_15] : k9_relat_1('#skF_4',A_15) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_286,c_26])).

tff(c_393,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( k7_relset_1(A_95,B_96,C_97,D_98) = k9_relat_1(C_97,D_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_395,plain,(
    ! [D_98] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_98) = k9_relat_1('#skF_4',D_98) ),
    inference(resolution,[status(thm)],[c_46,c_393])).

tff(c_397,plain,(
    ! [D_98] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_98) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_395])).

tff(c_398,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_42])).

tff(c_401,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_398])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:30:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.30  
% 2.24/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.31  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.24/1.31  
% 2.24/1.31  %Foreground sorts:
% 2.24/1.31  
% 2.24/1.31  
% 2.24/1.31  %Background operators:
% 2.24/1.31  
% 2.24/1.31  
% 2.24/1.31  %Foreground operators:
% 2.24/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.24/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.24/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.24/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.24/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.24/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.24/1.31  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.24/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.24/1.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.24/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.24/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.31  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.24/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.24/1.31  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.24/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.24/1.31  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.24/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.24/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.24/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.24/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.31  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.24/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.24/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.31  
% 2.55/1.32  tff(f_102, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 2.55/1.32  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.55/1.32  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 2.55/1.32  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.55/1.32  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 2.55/1.32  tff(f_90, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.55/1.32  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.55/1.32  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.55/1.32  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.55/1.32  tff(f_48, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 2.55/1.32  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.55/1.32  tff(f_60, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 2.55/1.32  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.55/1.32  tff(c_99, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.55/1.32  tff(c_103, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_99])).
% 2.55/1.32  tff(c_24, plain, (![B_14, A_13]: (r1_tarski(k9_relat_1(B_14, A_13), k2_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.55/1.32  tff(c_30, plain, (![A_16]: (k1_relat_1(A_16)!=k1_xboole_0 | k1_xboole_0=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.55/1.32  tff(c_116, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_103, c_30])).
% 2.55/1.32  tff(c_118, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_116])).
% 2.55/1.32  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.55/1.32  tff(c_158, plain, (![B_66, A_67]: (k1_tarski(k1_funct_1(B_66, A_67))=k2_relat_1(B_66) | k1_tarski(A_67)!=k1_relat_1(B_66) | ~v1_funct_1(B_66) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.55/1.32  tff(c_144, plain, (![A_61, B_62, C_63, D_64]: (k7_relset_1(A_61, B_62, C_63, D_64)=k9_relat_1(C_63, D_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.55/1.32  tff(c_147, plain, (![D_64]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_64)=k9_relat_1('#skF_4', D_64))), inference(resolution, [status(thm)], [c_46, c_144])).
% 2.55/1.32  tff(c_42, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.55/1.32  tff(c_148, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_42])).
% 2.55/1.32  tff(c_164, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_158, c_148])).
% 2.55/1.32  tff(c_182, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_50, c_164])).
% 2.55/1.32  tff(c_184, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_182])).
% 2.55/1.32  tff(c_120, plain, (![C_50, A_51, B_52]: (v4_relat_1(C_50, A_51) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.55/1.32  tff(c_124, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_120])).
% 2.55/1.32  tff(c_22, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(B_12), A_11) | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.55/1.32  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.55/1.32  tff(c_185, plain, (![B_68, C_69, A_70]: (k2_tarski(B_68, C_69)=A_70 | k1_tarski(C_69)=A_70 | k1_tarski(B_68)=A_70 | k1_xboole_0=A_70 | ~r1_tarski(A_70, k2_tarski(B_68, C_69)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.55/1.32  tff(c_201, plain, (![A_2, A_70]: (k2_tarski(A_2, A_2)=A_70 | k1_tarski(A_2)=A_70 | k1_tarski(A_2)=A_70 | k1_xboole_0=A_70 | ~r1_tarski(A_70, k1_tarski(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_185])).
% 2.55/1.32  tff(c_216, plain, (![A_71, A_72]: (k1_tarski(A_71)=A_72 | k1_tarski(A_71)=A_72 | k1_tarski(A_71)=A_72 | k1_xboole_0=A_72 | ~r1_tarski(A_72, k1_tarski(A_71)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_201])).
% 2.55/1.32  tff(c_236, plain, (![A_73, B_74]: (k1_tarski(A_73)=k1_relat_1(B_74) | k1_relat_1(B_74)=k1_xboole_0 | ~v4_relat_1(B_74, k1_tarski(A_73)) | ~v1_relat_1(B_74))), inference(resolution, [status(thm)], [c_22, c_216])).
% 2.55/1.32  tff(c_242, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_124, c_236])).
% 2.55/1.32  tff(c_245, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_103, c_242])).
% 2.55/1.32  tff(c_247, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_184, c_245])).
% 2.55/1.32  tff(c_248, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_182])).
% 2.55/1.32  tff(c_281, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_248])).
% 2.55/1.32  tff(c_285, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_281])).
% 2.55/1.32  tff(c_286, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_116])).
% 2.55/1.32  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.55/1.32  tff(c_292, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_286, c_2])).
% 2.55/1.32  tff(c_26, plain, (![A_15]: (k9_relat_1(k1_xboole_0, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.55/1.32  tff(c_291, plain, (![A_15]: (k9_relat_1('#skF_4', A_15)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_286, c_286, c_26])).
% 2.55/1.32  tff(c_393, plain, (![A_95, B_96, C_97, D_98]: (k7_relset_1(A_95, B_96, C_97, D_98)=k9_relat_1(C_97, D_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.55/1.32  tff(c_395, plain, (![D_98]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_98)=k9_relat_1('#skF_4', D_98))), inference(resolution, [status(thm)], [c_46, c_393])).
% 2.55/1.32  tff(c_397, plain, (![D_98]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_98)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_291, c_395])).
% 2.55/1.32  tff(c_398, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_397, c_42])).
% 2.55/1.32  tff(c_401, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_292, c_398])).
% 2.55/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.32  
% 2.55/1.32  Inference rules
% 2.55/1.32  ----------------------
% 2.55/1.32  #Ref     : 0
% 2.55/1.32  #Sup     : 73
% 2.55/1.32  #Fact    : 0
% 2.55/1.32  #Define  : 0
% 2.55/1.32  #Split   : 4
% 2.55/1.32  #Chain   : 0
% 2.55/1.32  #Close   : 0
% 2.55/1.32  
% 2.55/1.32  Ordering : KBO
% 2.55/1.32  
% 2.55/1.32  Simplification rules
% 2.55/1.32  ----------------------
% 2.55/1.32  #Subsume      : 1
% 2.55/1.32  #Demod        : 47
% 2.55/1.32  #Tautology    : 43
% 2.55/1.32  #SimpNegUnit  : 1
% 2.55/1.32  #BackRed      : 12
% 2.55/1.32  
% 2.55/1.32  #Partial instantiations: 0
% 2.55/1.32  #Strategies tried      : 1
% 2.55/1.32  
% 2.55/1.32  Timing (in seconds)
% 2.55/1.32  ----------------------
% 2.55/1.32  Preprocessing        : 0.34
% 2.55/1.32  Parsing              : 0.18
% 2.55/1.33  CNF conversion       : 0.02
% 2.55/1.33  Main loop            : 0.26
% 2.55/1.33  Inferencing          : 0.09
% 2.55/1.33  Reduction            : 0.09
% 2.55/1.33  Demodulation         : 0.06
% 2.55/1.33  BG Simplification    : 0.02
% 2.55/1.33  Subsumption          : 0.04
% 2.55/1.33  Abstraction          : 0.01
% 2.55/1.33  MUC search           : 0.00
% 2.55/1.33  Cooper               : 0.00
% 2.55/1.33  Total                : 0.63
% 2.55/1.33  Index Insertion      : 0.00
% 2.55/1.33  Index Deletion       : 0.00
% 2.55/1.33  Index Matching       : 0.00
% 2.55/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------

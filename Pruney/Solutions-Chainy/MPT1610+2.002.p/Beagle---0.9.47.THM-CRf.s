%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:29 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   79 (  96 expanded)
%              Number of leaves         :   49 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :   72 ( 123 expanded)
%              Number of equality atoms :   39 (  67 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v4_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k3_tarski > k3_lattice3 > k2_yellow_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_ordinal1 > k1_lattice3 > o_0_0_xboole_0 > k6_numbers > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k6_numbers,type,(
    k6_numbers: $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_lattice3,type,(
    k3_lattice3: $i > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff(k1_lattice3,type,(
    k1_lattice3: $i > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_ordinal1,type,(
    v4_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_72,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ~ ( ~ ( A = k1_xboole_0
            & B != k1_xboole_0 )
        & ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ~ ( B = k1_relat_1(C)
                & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_107,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_119,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_117,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k1_xboole_0,A)
       => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_122,negated_conjecture,(
    ~ ! [A] : k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_1)).

tff(f_67,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_105,axiom,(
    ! [A] : k6_subset_1(k1_ordinal1(A),k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_ordinal1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_50,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_62,plain,(
    ! [A_30] : k1_relat_1('#skF_3'(A_30,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_70,plain,(
    ! [A_30] : v1_relat_1('#skF_3'(A_30,k1_xboole_0)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_293,plain,(
    ! [A_74] :
      ( k1_relat_1(A_74) != k1_xboole_0
      | k1_xboole_0 = A_74
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_299,plain,(
    ! [A_30] :
      ( k1_relat_1('#skF_3'(A_30,k1_xboole_0)) != k1_xboole_0
      | '#skF_3'(A_30,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_70,c_293])).

tff(c_303,plain,(
    ! [A_30] : '#skF_3'(A_30,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_299])).

tff(c_58,plain,(
    ! [A_30] : r1_tarski(k2_relat_1('#skF_3'(A_30,k1_xboole_0)),A_30) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_313,plain,(
    ! [A_30] : r1_tarski(k2_relat_1(k1_xboole_0),A_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_58])).

tff(c_317,plain,(
    ! [A_30] : r1_tarski(k1_xboole_0,A_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_313])).

tff(c_24,plain,(
    ! [C_18,A_14] :
      ( r2_hidden(C_18,k1_zfmisc_1(A_14))
      | ~ r1_tarski(C_18,A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_82,plain,(
    ! [A_36] : k9_setfam_1(A_36) = k1_zfmisc_1(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_90,plain,(
    ! [A_39] : k2_yellow_1(k9_setfam_1(A_39)) = k3_yellow_1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_93,plain,(
    ! [A_39] : k2_yellow_1(k1_zfmisc_1(A_39)) = k3_yellow_1(A_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_90])).

tff(c_452,plain,(
    ! [A_94] :
      ( k3_yellow_0(k2_yellow_1(A_94)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,A_94)
      | v1_xboole_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_687,plain,(
    ! [A_130] :
      ( k3_yellow_0(k3_yellow_1(A_130)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(A_130))
      | v1_xboole_0(k1_zfmisc_1(A_130)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_452])).

tff(c_691,plain,(
    ! [A_14] :
      ( k3_yellow_0(k3_yellow_1(A_14)) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_14))
      | ~ r1_tarski(k1_xboole_0,A_14) ) ),
    inference(resolution,[status(thm)],[c_24,c_687])).

tff(c_695,plain,(
    ! [A_131] :
      ( k3_yellow_0(k3_yellow_1(A_131)) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_131)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_691])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_700,plain,(
    ! [A_132] :
      ( k1_zfmisc_1(A_132) = k1_xboole_0
      | k3_yellow_0(k3_yellow_1(A_132)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_695,c_4])).

tff(c_92,plain,(
    k3_yellow_0(k3_yellow_1('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_711,plain,(
    k1_zfmisc_1('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_700,c_92])).

tff(c_240,plain,(
    ! [C_67,A_68] :
      ( r2_hidden(C_67,k1_zfmisc_1(A_68))
      | ~ r1_tarski(C_67,A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_197,plain,(
    ! [A_58,B_59] : k6_subset_1(A_58,B_59) = k4_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_80,plain,(
    ! [A_35] : k6_subset_1(k1_ordinal1(A_35),k1_tarski(A_35)) = A_35 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_226,plain,(
    ! [A_65] : k4_xboole_0(k1_ordinal1(A_65),k1_tarski(A_65)) = A_65 ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_80])).

tff(c_38,plain,(
    ! [C_21,B_20] : ~ r2_hidden(C_21,k4_xboole_0(B_20,k1_tarski(C_21))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_232,plain,(
    ! [A_65] : ~ r2_hidden(A_65,A_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_38])).

tff(c_245,plain,(
    ! [A_68] : ~ r1_tarski(k1_zfmisc_1(A_68),A_68) ),
    inference(resolution,[status(thm)],[c_240,c_232])).

tff(c_740,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_711,c_245])).

tff(c_755,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_740])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:38:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.43  
% 3.02/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.43  %$ r2_hidden > r1_tarski > v4_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k3_tarski > k3_lattice3 > k2_yellow_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_ordinal1 > k1_lattice3 > o_0_0_xboole_0 > k6_numbers > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.02/1.43  
% 3.02/1.43  %Foreground sorts:
% 3.02/1.43  
% 3.02/1.43  
% 3.02/1.43  %Background operators:
% 3.02/1.43  
% 3.02/1.43  
% 3.02/1.43  %Foreground operators:
% 3.02/1.43  tff(k6_numbers, type, k6_numbers: $i).
% 3.02/1.43  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 3.02/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.02/1.43  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 3.02/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.43  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 3.02/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.02/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.02/1.43  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.02/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.02/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.02/1.43  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.02/1.43  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 3.02/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.02/1.43  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.02/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.02/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.02/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.02/1.43  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 3.02/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.02/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.02/1.43  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.02/1.43  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.02/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.02/1.43  tff(v4_ordinal1, type, v4_ordinal1: $i > $o).
% 3.02/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.43  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.02/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.02/1.43  tff('#skF_4', type, '#skF_4': $i).
% 3.02/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.02/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.02/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.02/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.02/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.02/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.02/1.43  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.02/1.43  
% 3.02/1.44  tff(f_72, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.02/1.44  tff(f_97, axiom, (![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 3.02/1.44  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.02/1.44  tff(f_53, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.02/1.44  tff(f_107, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 3.02/1.44  tff(f_119, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 3.02/1.44  tff(f_117, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow_1)).
% 3.02/1.44  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.02/1.44  tff(f_122, negated_conjecture, ~(![A]: (k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_yellow_1)).
% 3.02/1.44  tff(f_67, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.02/1.44  tff(f_105, axiom, (![A]: (k6_subset_1(k1_ordinal1(A), k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_ordinal1)).
% 3.02/1.44  tff(f_61, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 3.02/1.44  tff(c_50, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.02/1.44  tff(c_62, plain, (![A_30]: (k1_relat_1('#skF_3'(A_30, k1_xboole_0))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.02/1.44  tff(c_70, plain, (![A_30]: (v1_relat_1('#skF_3'(A_30, k1_xboole_0)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.02/1.44  tff(c_293, plain, (![A_74]: (k1_relat_1(A_74)!=k1_xboole_0 | k1_xboole_0=A_74 | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.02/1.44  tff(c_299, plain, (![A_30]: (k1_relat_1('#skF_3'(A_30, k1_xboole_0))!=k1_xboole_0 | '#skF_3'(A_30, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_70, c_293])).
% 3.02/1.44  tff(c_303, plain, (![A_30]: ('#skF_3'(A_30, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_299])).
% 3.02/1.44  tff(c_58, plain, (![A_30]: (r1_tarski(k2_relat_1('#skF_3'(A_30, k1_xboole_0)), A_30))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.02/1.44  tff(c_313, plain, (![A_30]: (r1_tarski(k2_relat_1(k1_xboole_0), A_30))), inference(demodulation, [status(thm), theory('equality')], [c_303, c_58])).
% 3.02/1.44  tff(c_317, plain, (![A_30]: (r1_tarski(k1_xboole_0, A_30))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_313])).
% 3.02/1.44  tff(c_24, plain, (![C_18, A_14]: (r2_hidden(C_18, k1_zfmisc_1(A_14)) | ~r1_tarski(C_18, A_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.02/1.44  tff(c_82, plain, (![A_36]: (k9_setfam_1(A_36)=k1_zfmisc_1(A_36))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.02/1.44  tff(c_90, plain, (![A_39]: (k2_yellow_1(k9_setfam_1(A_39))=k3_yellow_1(A_39))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.02/1.44  tff(c_93, plain, (![A_39]: (k2_yellow_1(k1_zfmisc_1(A_39))=k3_yellow_1(A_39))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_90])).
% 3.02/1.44  tff(c_452, plain, (![A_94]: (k3_yellow_0(k2_yellow_1(A_94))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, A_94) | v1_xboole_0(A_94))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.02/1.44  tff(c_687, plain, (![A_130]: (k3_yellow_0(k3_yellow_1(A_130))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, k1_zfmisc_1(A_130)) | v1_xboole_0(k1_zfmisc_1(A_130)))), inference(superposition, [status(thm), theory('equality')], [c_93, c_452])).
% 3.02/1.44  tff(c_691, plain, (![A_14]: (k3_yellow_0(k3_yellow_1(A_14))=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_14)) | ~r1_tarski(k1_xboole_0, A_14))), inference(resolution, [status(thm)], [c_24, c_687])).
% 3.02/1.44  tff(c_695, plain, (![A_131]: (k3_yellow_0(k3_yellow_1(A_131))=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_131)))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_691])).
% 3.02/1.44  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.02/1.44  tff(c_700, plain, (![A_132]: (k1_zfmisc_1(A_132)=k1_xboole_0 | k3_yellow_0(k3_yellow_1(A_132))=k1_xboole_0)), inference(resolution, [status(thm)], [c_695, c_4])).
% 3.02/1.44  tff(c_92, plain, (k3_yellow_0(k3_yellow_1('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.02/1.44  tff(c_711, plain, (k1_zfmisc_1('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_700, c_92])).
% 3.02/1.44  tff(c_240, plain, (![C_67, A_68]: (r2_hidden(C_67, k1_zfmisc_1(A_68)) | ~r1_tarski(C_67, A_68))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.02/1.44  tff(c_197, plain, (![A_58, B_59]: (k6_subset_1(A_58, B_59)=k4_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.02/1.44  tff(c_80, plain, (![A_35]: (k6_subset_1(k1_ordinal1(A_35), k1_tarski(A_35))=A_35)), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.02/1.44  tff(c_226, plain, (![A_65]: (k4_xboole_0(k1_ordinal1(A_65), k1_tarski(A_65))=A_65)), inference(superposition, [status(thm), theory('equality')], [c_197, c_80])).
% 3.02/1.44  tff(c_38, plain, (![C_21, B_20]: (~r2_hidden(C_21, k4_xboole_0(B_20, k1_tarski(C_21))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.02/1.44  tff(c_232, plain, (![A_65]: (~r2_hidden(A_65, A_65))), inference(superposition, [status(thm), theory('equality')], [c_226, c_38])).
% 3.02/1.44  tff(c_245, plain, (![A_68]: (~r1_tarski(k1_zfmisc_1(A_68), A_68))), inference(resolution, [status(thm)], [c_240, c_232])).
% 3.02/1.44  tff(c_740, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_711, c_245])).
% 3.02/1.44  tff(c_755, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_317, c_740])).
% 3.02/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.44  
% 3.02/1.44  Inference rules
% 3.02/1.44  ----------------------
% 3.02/1.44  #Ref     : 0
% 3.02/1.44  #Sup     : 145
% 3.02/1.44  #Fact    : 0
% 3.02/1.44  #Define  : 0
% 3.02/1.44  #Split   : 0
% 3.02/1.44  #Chain   : 0
% 3.02/1.44  #Close   : 0
% 3.02/1.44  
% 3.02/1.44  Ordering : KBO
% 3.02/1.44  
% 3.02/1.44  Simplification rules
% 3.02/1.44  ----------------------
% 3.02/1.44  #Subsume      : 1
% 3.02/1.44  #Demod        : 24
% 3.02/1.44  #Tautology    : 83
% 3.02/1.44  #SimpNegUnit  : 1
% 3.02/1.44  #BackRed      : 4
% 3.02/1.44  
% 3.02/1.44  #Partial instantiations: 0
% 3.02/1.44  #Strategies tried      : 1
% 3.02/1.44  
% 3.02/1.44  Timing (in seconds)
% 3.02/1.44  ----------------------
% 3.02/1.45  Preprocessing        : 0.34
% 3.02/1.45  Parsing              : 0.17
% 3.02/1.45  CNF conversion       : 0.02
% 3.02/1.45  Main loop            : 0.32
% 3.02/1.45  Inferencing          : 0.12
% 3.02/1.45  Reduction            : 0.10
% 3.02/1.45  Demodulation         : 0.07
% 3.02/1.45  BG Simplification    : 0.02
% 3.02/1.45  Subsumption          : 0.05
% 3.02/1.45  Abstraction          : 0.02
% 3.02/1.45  MUC search           : 0.00
% 3.02/1.45  Cooper               : 0.00
% 3.02/1.45  Total                : 0.69
% 3.02/1.45  Index Insertion      : 0.00
% 3.02/1.45  Index Deletion       : 0.00
% 3.02/1.45  Index Matching       : 0.00
% 3.02/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------

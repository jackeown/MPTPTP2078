%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:20 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 116 expanded)
%              Number of leaves         :   41 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :  118 ( 191 expanded)
%              Number of equality atoms :   55 (  85 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

tff(f_58,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_79,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_66,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k2_relat_1(B))
      <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_60,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_161,plain,(
    ! [A_61,B_62,C_63] : k2_enumset1(A_61,A_61,B_62,C_63) = k1_enumset1(A_61,B_62,C_63) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [F_14,A_7,C_9,D_10] : r2_hidden(F_14,k2_enumset1(A_7,F_14,C_9,D_10)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_182,plain,(
    ! [A_64,B_65,C_66] : r2_hidden(A_64,k1_enumset1(A_64,B_65,C_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_14])).

tff(c_186,plain,(
    ! [A_67,B_68] : r2_hidden(A_67,k2_tarski(A_67,B_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_182])).

tff(c_189,plain,(
    ! [A_1] : r2_hidden(A_1,k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_186])).

tff(c_40,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_54,plain,(
    ! [A_24] : m1_subset_1(k6_partfun1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_136,plain,(
    ! [B_57,A_58] :
      ( v1_relat_1(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58))
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_139,plain,(
    ! [A_24] :
      ( v1_relat_1(k6_partfun1(A_24))
      | ~ v1_relat_1(k2_zfmisc_1(A_24,A_24)) ) ),
    inference(resolution,[status(thm)],[c_54,c_136])).

tff(c_145,plain,(
    ! [A_24] : v1_relat_1(k6_partfun1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_139])).

tff(c_56,plain,(
    ! [A_25] : k6_relat_1(A_25) = k6_partfun1(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_44,plain,(
    ! [A_21] : k1_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_70,plain,(
    ! [A_21] : k1_relat_1(k6_partfun1(A_21)) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_44])).

tff(c_46,plain,(
    ! [A_21] : k2_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_69,plain,(
    ! [A_21] : k2_relat_1(k6_partfun1(A_21)) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46])).

tff(c_123,plain,(
    ! [A_56] :
      ( k10_relat_1(A_56,k2_relat_1(A_56)) = k1_relat_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_132,plain,(
    ! [A_21] :
      ( k10_relat_1(k6_partfun1(A_21),A_21) = k1_relat_1(k6_partfun1(A_21))
      | ~ v1_relat_1(k6_partfun1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_123])).

tff(c_135,plain,(
    ! [A_21] :
      ( k10_relat_1(k6_partfun1(A_21),A_21) = A_21
      | ~ v1_relat_1(k6_partfun1(A_21)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_132])).

tff(c_151,plain,(
    ! [A_21] : k10_relat_1(k6_partfun1(A_21),A_21) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_135])).

tff(c_190,plain,(
    ! [B_69,A_70] :
      ( k10_relat_1(B_69,k1_tarski(A_70)) != k1_xboole_0
      | ~ r2_hidden(A_70,k2_relat_1(B_69))
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_193,plain,(
    ! [A_21,A_70] :
      ( k10_relat_1(k6_partfun1(A_21),k1_tarski(A_70)) != k1_xboole_0
      | ~ r2_hidden(A_70,A_21)
      | ~ v1_relat_1(k6_partfun1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_190])).

tff(c_241,plain,(
    ! [A_84,A_85] :
      ( k10_relat_1(k6_partfun1(A_84),k1_tarski(A_85)) != k1_xboole_0
      | ~ r2_hidden(A_85,A_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_193])).

tff(c_248,plain,(
    ! [A_85] :
      ( k1_tarski(A_85) != k1_xboole_0
      | ~ r2_hidden(A_85,k1_tarski(A_85)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_241])).

tff(c_251,plain,(
    ! [A_85] : k1_tarski(A_85) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_248])).

tff(c_68,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_66,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_62,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_340,plain,(
    ! [D_121,C_122,B_123,A_124] :
      ( r2_hidden(k1_funct_1(D_121,C_122),B_123)
      | k1_xboole_0 = B_123
      | ~ r2_hidden(C_122,A_124)
      | ~ m1_subset_1(D_121,k1_zfmisc_1(k2_zfmisc_1(A_124,B_123)))
      | ~ v1_funct_2(D_121,A_124,B_123)
      | ~ v1_funct_1(D_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_377,plain,(
    ! [D_125,B_126] :
      ( r2_hidden(k1_funct_1(D_125,'#skF_5'),B_126)
      | k1_xboole_0 = B_126
      | ~ m1_subset_1(D_125,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_126)))
      | ~ v1_funct_2(D_125,'#skF_3',B_126)
      | ~ v1_funct_1(D_125) ) ),
    inference(resolution,[status(thm)],[c_62,c_340])).

tff(c_384,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_377])).

tff(c_388,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_384])).

tff(c_389,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_251,c_388])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_253,plain,(
    ! [C_89,B_88,F_90,A_91,D_87] :
      ( F_90 = D_87
      | F_90 = C_89
      | F_90 = B_88
      | F_90 = A_91
      | ~ r2_hidden(F_90,k2_enumset1(A_91,B_88,C_89,D_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_277,plain,(
    ! [F_92,C_93,B_94,A_95] :
      ( F_92 = C_93
      | F_92 = B_94
      | F_92 = A_95
      | F_92 = A_95
      | ~ r2_hidden(F_92,k1_enumset1(A_95,B_94,C_93)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_253])).

tff(c_296,plain,(
    ! [F_96,B_97,A_98] :
      ( F_96 = B_97
      | F_96 = A_98
      | F_96 = A_98
      | F_96 = A_98
      | ~ r2_hidden(F_96,k2_tarski(A_98,B_97)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_277])).

tff(c_305,plain,(
    ! [F_96,A_1] :
      ( F_96 = A_1
      | F_96 = A_1
      | F_96 = A_1
      | F_96 = A_1
      | ~ r2_hidden(F_96,k1_tarski(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_296])).

tff(c_423,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_389,c_305])).

tff(c_428,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_60,c_60,c_60,c_423])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.36  
% 2.57/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.37  %$ v1_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4
% 2.57/1.37  
% 2.57/1.37  %Foreground sorts:
% 2.57/1.37  
% 2.57/1.37  
% 2.57/1.37  %Background operators:
% 2.57/1.37  
% 2.57/1.37  
% 2.57/1.37  %Foreground operators:
% 2.57/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.57/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.57/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.57/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.57/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.57/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.57/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.57/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.57/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.57/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.57/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.57/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.57/1.37  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.57/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.57/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.57/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.57/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.57/1.37  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.57/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.37  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.57/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.57/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.57/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.57/1.37  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.57/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.57/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.57/1.37  
% 2.69/1.38  tff(f_102, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.69/1.38  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.69/1.38  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.69/1.38  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.69/1.38  tff(f_49, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_enumset1)).
% 2.69/1.38  tff(f_58, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.69/1.38  tff(f_77, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.69/1.38  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.69/1.38  tff(f_79, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.69/1.38  tff(f_66, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.69/1.38  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.69/1.38  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 2.69/1.38  tff(f_91, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.69/1.38  tff(c_60, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.69/1.38  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.69/1.38  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.69/1.38  tff(c_161, plain, (![A_61, B_62, C_63]: (k2_enumset1(A_61, A_61, B_62, C_63)=k1_enumset1(A_61, B_62, C_63))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.69/1.38  tff(c_14, plain, (![F_14, A_7, C_9, D_10]: (r2_hidden(F_14, k2_enumset1(A_7, F_14, C_9, D_10)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.69/1.38  tff(c_182, plain, (![A_64, B_65, C_66]: (r2_hidden(A_64, k1_enumset1(A_64, B_65, C_66)))), inference(superposition, [status(thm), theory('equality')], [c_161, c_14])).
% 2.69/1.38  tff(c_186, plain, (![A_67, B_68]: (r2_hidden(A_67, k2_tarski(A_67, B_68)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_182])).
% 2.69/1.38  tff(c_189, plain, (![A_1]: (r2_hidden(A_1, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_186])).
% 2.69/1.38  tff(c_40, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.69/1.38  tff(c_54, plain, (![A_24]: (m1_subset_1(k6_partfun1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.69/1.38  tff(c_136, plain, (![B_57, A_58]: (v1_relat_1(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.69/1.38  tff(c_139, plain, (![A_24]: (v1_relat_1(k6_partfun1(A_24)) | ~v1_relat_1(k2_zfmisc_1(A_24, A_24)))), inference(resolution, [status(thm)], [c_54, c_136])).
% 2.69/1.38  tff(c_145, plain, (![A_24]: (v1_relat_1(k6_partfun1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_139])).
% 2.69/1.38  tff(c_56, plain, (![A_25]: (k6_relat_1(A_25)=k6_partfun1(A_25))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.69/1.38  tff(c_44, plain, (![A_21]: (k1_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.69/1.38  tff(c_70, plain, (![A_21]: (k1_relat_1(k6_partfun1(A_21))=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_44])).
% 2.69/1.38  tff(c_46, plain, (![A_21]: (k2_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.69/1.38  tff(c_69, plain, (![A_21]: (k2_relat_1(k6_partfun1(A_21))=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46])).
% 2.69/1.38  tff(c_123, plain, (![A_56]: (k10_relat_1(A_56, k2_relat_1(A_56))=k1_relat_1(A_56) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.69/1.38  tff(c_132, plain, (![A_21]: (k10_relat_1(k6_partfun1(A_21), A_21)=k1_relat_1(k6_partfun1(A_21)) | ~v1_relat_1(k6_partfun1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_69, c_123])).
% 2.69/1.38  tff(c_135, plain, (![A_21]: (k10_relat_1(k6_partfun1(A_21), A_21)=A_21 | ~v1_relat_1(k6_partfun1(A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_132])).
% 2.69/1.38  tff(c_151, plain, (![A_21]: (k10_relat_1(k6_partfun1(A_21), A_21)=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_145, c_135])).
% 2.69/1.38  tff(c_190, plain, (![B_69, A_70]: (k10_relat_1(B_69, k1_tarski(A_70))!=k1_xboole_0 | ~r2_hidden(A_70, k2_relat_1(B_69)) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.69/1.38  tff(c_193, plain, (![A_21, A_70]: (k10_relat_1(k6_partfun1(A_21), k1_tarski(A_70))!=k1_xboole_0 | ~r2_hidden(A_70, A_21) | ~v1_relat_1(k6_partfun1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_69, c_190])).
% 2.69/1.38  tff(c_241, plain, (![A_84, A_85]: (k10_relat_1(k6_partfun1(A_84), k1_tarski(A_85))!=k1_xboole_0 | ~r2_hidden(A_85, A_84))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_193])).
% 2.69/1.38  tff(c_248, plain, (![A_85]: (k1_tarski(A_85)!=k1_xboole_0 | ~r2_hidden(A_85, k1_tarski(A_85)))), inference(superposition, [status(thm), theory('equality')], [c_151, c_241])).
% 2.69/1.38  tff(c_251, plain, (![A_85]: (k1_tarski(A_85)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_189, c_248])).
% 2.69/1.38  tff(c_68, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.69/1.38  tff(c_66, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.69/1.38  tff(c_64, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.69/1.38  tff(c_62, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.69/1.38  tff(c_340, plain, (![D_121, C_122, B_123, A_124]: (r2_hidden(k1_funct_1(D_121, C_122), B_123) | k1_xboole_0=B_123 | ~r2_hidden(C_122, A_124) | ~m1_subset_1(D_121, k1_zfmisc_1(k2_zfmisc_1(A_124, B_123))) | ~v1_funct_2(D_121, A_124, B_123) | ~v1_funct_1(D_121))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.69/1.38  tff(c_377, plain, (![D_125, B_126]: (r2_hidden(k1_funct_1(D_125, '#skF_5'), B_126) | k1_xboole_0=B_126 | ~m1_subset_1(D_125, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_126))) | ~v1_funct_2(D_125, '#skF_3', B_126) | ~v1_funct_1(D_125))), inference(resolution, [status(thm)], [c_62, c_340])).
% 2.69/1.38  tff(c_384, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_64, c_377])).
% 2.69/1.38  tff(c_388, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_384])).
% 2.69/1.38  tff(c_389, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_251, c_388])).
% 2.69/1.38  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.69/1.38  tff(c_253, plain, (![C_89, B_88, F_90, A_91, D_87]: (F_90=D_87 | F_90=C_89 | F_90=B_88 | F_90=A_91 | ~r2_hidden(F_90, k2_enumset1(A_91, B_88, C_89, D_87)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.69/1.38  tff(c_277, plain, (![F_92, C_93, B_94, A_95]: (F_92=C_93 | F_92=B_94 | F_92=A_95 | F_92=A_95 | ~r2_hidden(F_92, k1_enumset1(A_95, B_94, C_93)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_253])).
% 2.69/1.38  tff(c_296, plain, (![F_96, B_97, A_98]: (F_96=B_97 | F_96=A_98 | F_96=A_98 | F_96=A_98 | ~r2_hidden(F_96, k2_tarski(A_98, B_97)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_277])).
% 2.69/1.38  tff(c_305, plain, (![F_96, A_1]: (F_96=A_1 | F_96=A_1 | F_96=A_1 | F_96=A_1 | ~r2_hidden(F_96, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_296])).
% 2.69/1.38  tff(c_423, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_389, c_305])).
% 2.69/1.38  tff(c_428, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_60, c_60, c_60, c_423])).
% 2.69/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.38  
% 2.69/1.38  Inference rules
% 2.69/1.38  ----------------------
% 2.69/1.38  #Ref     : 0
% 2.69/1.38  #Sup     : 76
% 2.69/1.38  #Fact    : 0
% 2.69/1.38  #Define  : 0
% 2.69/1.38  #Split   : 0
% 2.69/1.38  #Chain   : 0
% 2.69/1.38  #Close   : 0
% 2.69/1.38  
% 2.69/1.38  Ordering : KBO
% 2.69/1.38  
% 2.69/1.38  Simplification rules
% 2.69/1.38  ----------------------
% 2.69/1.38  #Subsume      : 0
% 2.69/1.38  #Demod        : 16
% 2.69/1.38  #Tautology    : 35
% 2.69/1.38  #SimpNegUnit  : 2
% 2.69/1.38  #BackRed      : 0
% 2.69/1.38  
% 2.69/1.38  #Partial instantiations: 0
% 2.69/1.38  #Strategies tried      : 1
% 2.69/1.38  
% 2.69/1.38  Timing (in seconds)
% 2.69/1.38  ----------------------
% 2.69/1.38  Preprocessing        : 0.33
% 2.69/1.38  Parsing              : 0.17
% 2.69/1.38  CNF conversion       : 0.02
% 2.69/1.38  Main loop            : 0.27
% 2.69/1.38  Inferencing          : 0.10
% 2.69/1.38  Reduction            : 0.08
% 2.69/1.38  Demodulation         : 0.06
% 2.69/1.38  BG Simplification    : 0.02
% 2.69/1.38  Subsumption          : 0.06
% 2.69/1.38  Abstraction          : 0.02
% 2.69/1.38  MUC search           : 0.00
% 2.69/1.38  Cooper               : 0.00
% 2.69/1.38  Total                : 0.64
% 2.69/1.38  Index Insertion      : 0.00
% 2.69/1.39  Index Deletion       : 0.00
% 2.69/1.39  Index Matching       : 0.00
% 2.69/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:12 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 130 expanded)
%              Number of leaves         :   31 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :  105 ( 256 expanded)
%              Number of equality atoms :   29 (  64 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_32,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_30,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_61,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_74,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_61])).

tff(c_77,plain,(
    ! [A_53] :
      ( k1_relat_1(A_53) = k1_xboole_0
      | k2_relat_1(A_53) != k1_xboole_0
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_85,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_74,c_77])).

tff(c_86,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_359,plain,(
    ! [A_99,B_100,C_101] :
      ( k2_relset_1(A_99,B_100,C_101) = k2_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_377,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_359])).

tff(c_6,plain,(
    ! [A_3] : m1_subset_1('#skF_1'(A_3),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_116,plain,(
    ! [B_61,A_62] :
      ( m1_subset_1(k1_tarski(B_61),k1_zfmisc_1(A_62))
      | k1_xboole_0 = A_62
      | ~ m1_subset_1(B_61,A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_126,plain,(
    ! [B_63,A_64] :
      ( r1_tarski(k1_tarski(B_63),A_64)
      | k1_xboole_0 = A_64
      | ~ m1_subset_1(B_63,A_64) ) ),
    inference(resolution,[status(thm)],[c_116,c_10])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | ~ r1_tarski(k1_tarski(A_1),B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_136,plain,(
    ! [B_65,A_66] :
      ( r2_hidden(B_65,A_66)
      | k1_xboole_0 = A_66
      | ~ m1_subset_1(B_65,A_66) ) ),
    inference(resolution,[status(thm)],[c_126,c_2])).

tff(c_28,plain,(
    ! [D_36] :
      ( ~ r2_hidden(D_36,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(D_36,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_146,plain,(
    ! [B_65] :
      ( ~ m1_subset_1(B_65,'#skF_3')
      | k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | ~ m1_subset_1(B_65,k2_relset_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_136,c_28])).

tff(c_173,plain,(
    ! [B_76] :
      ( ~ m1_subset_1(B_76,'#skF_3')
      | ~ m1_subset_1(B_76,k2_relset_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_178,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_173])).

tff(c_379,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_178])).

tff(c_447,plain,(
    ! [A_111,B_112,C_113] :
      ( m1_subset_1(k2_relset_1(A_111,B_112,C_113),k1_zfmisc_1(B_112))
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_467,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_447])).

tff(c_474,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_467])).

tff(c_481,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_474,c_10])).

tff(c_135,plain,(
    ! [B_63,A_64] :
      ( r2_hidden(B_63,A_64)
      | k1_xboole_0 = A_64
      | ~ m1_subset_1(B_63,A_64) ) ),
    inference(resolution,[status(thm)],[c_126,c_2])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_147,plain,(
    ! [A_67,C_68,B_69] :
      ( m1_subset_1(A_67,C_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(C_68))
      | ~ r2_hidden(A_67,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_168,plain,(
    ! [A_73,B_74,A_75] :
      ( m1_subset_1(A_73,B_74)
      | ~ r2_hidden(A_73,A_75)
      | ~ r1_tarski(A_75,B_74) ) ),
    inference(resolution,[status(thm)],[c_12,c_147])).

tff(c_171,plain,(
    ! [B_63,B_74,A_64] :
      ( m1_subset_1(B_63,B_74)
      | ~ r1_tarski(A_64,B_74)
      | k1_xboole_0 = A_64
      | ~ m1_subset_1(B_63,A_64) ) ),
    inference(resolution,[status(thm)],[c_135,c_168])).

tff(c_483,plain,(
    ! [B_63] :
      ( m1_subset_1(B_63,'#skF_3')
      | k2_relat_1('#skF_4') = k1_xboole_0
      | ~ m1_subset_1(B_63,k2_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_481,c_171])).

tff(c_495,plain,(
    ! [B_115] :
      ( m1_subset_1(B_115,'#skF_3')
      | ~ m1_subset_1(B_115,k2_relat_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_483])).

tff(c_499,plain,(
    m1_subset_1('#skF_1'(k2_relat_1('#skF_4')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_495])).

tff(c_503,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_379,c_499])).

tff(c_504,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_571,plain,(
    ! [A_124,B_125,C_126] :
      ( k2_relset_1(A_124,B_125,C_126) = k2_relat_1(C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_582,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_571])).

tff(c_590,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_582])).

tff(c_592,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_590])).

tff(c_593,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_801,plain,(
    ! [A_163,B_164,C_165] :
      ( k1_relset_1(A_163,B_164,C_165) = k1_relat_1(C_165)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_812,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_801])).

tff(c_820,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_812])).

tff(c_822,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_820])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:54:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.56  
% 3.09/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.56  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.09/1.56  
% 3.09/1.56  %Foreground sorts:
% 3.09/1.56  
% 3.09/1.56  
% 3.09/1.56  %Background operators:
% 3.09/1.56  
% 3.09/1.56  
% 3.09/1.56  %Foreground operators:
% 3.09/1.56  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.09/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.09/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.09/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.09/1.56  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.09/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.09/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.09/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.09/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.09/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.09/1.56  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.09/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.09/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.09/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.09/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.09/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.09/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.09/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.09/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.09/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.09/1.56  
% 3.27/1.58  tff(f_92, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 3.27/1.58  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.27/1.58  tff(f_55, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 3.27/1.58  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.27/1.58  tff(f_32, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 3.27/1.58  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 3.27/1.58  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.27/1.58  tff(f_29, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.27/1.58  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.27/1.58  tff(f_49, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.27/1.58  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.27/1.58  tff(c_30, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.27/1.58  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.27/1.58  tff(c_61, plain, (![C_48, A_49, B_50]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.27/1.58  tff(c_74, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_61])).
% 3.27/1.58  tff(c_77, plain, (![A_53]: (k1_relat_1(A_53)=k1_xboole_0 | k2_relat_1(A_53)!=k1_xboole_0 | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.27/1.58  tff(c_85, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_74, c_77])).
% 3.27/1.58  tff(c_86, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_85])).
% 3.27/1.58  tff(c_359, plain, (![A_99, B_100, C_101]: (k2_relset_1(A_99, B_100, C_101)=k2_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.27/1.58  tff(c_377, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_359])).
% 3.27/1.58  tff(c_6, plain, (![A_3]: (m1_subset_1('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.27/1.58  tff(c_116, plain, (![B_61, A_62]: (m1_subset_1(k1_tarski(B_61), k1_zfmisc_1(A_62)) | k1_xboole_0=A_62 | ~m1_subset_1(B_61, A_62))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.27/1.58  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.27/1.58  tff(c_126, plain, (![B_63, A_64]: (r1_tarski(k1_tarski(B_63), A_64) | k1_xboole_0=A_64 | ~m1_subset_1(B_63, A_64))), inference(resolution, [status(thm)], [c_116, c_10])).
% 3.27/1.58  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | ~r1_tarski(k1_tarski(A_1), B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.27/1.58  tff(c_136, plain, (![B_65, A_66]: (r2_hidden(B_65, A_66) | k1_xboole_0=A_66 | ~m1_subset_1(B_65, A_66))), inference(resolution, [status(thm)], [c_126, c_2])).
% 3.27/1.58  tff(c_28, plain, (![D_36]: (~r2_hidden(D_36, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(D_36, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.27/1.58  tff(c_146, plain, (![B_65]: (~m1_subset_1(B_65, '#skF_3') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | ~m1_subset_1(B_65, k2_relset_1('#skF_2', '#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_136, c_28])).
% 3.27/1.58  tff(c_173, plain, (![B_76]: (~m1_subset_1(B_76, '#skF_3') | ~m1_subset_1(B_76, k2_relset_1('#skF_2', '#skF_3', '#skF_4')))), inference(splitLeft, [status(thm)], [c_146])).
% 3.27/1.58  tff(c_178, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3')), inference(resolution, [status(thm)], [c_6, c_173])).
% 3.27/1.58  tff(c_379, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_377, c_178])).
% 3.27/1.58  tff(c_447, plain, (![A_111, B_112, C_113]: (m1_subset_1(k2_relset_1(A_111, B_112, C_113), k1_zfmisc_1(B_112)) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.27/1.58  tff(c_467, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_377, c_447])).
% 3.27/1.58  tff(c_474, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_467])).
% 3.27/1.58  tff(c_481, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_474, c_10])).
% 3.27/1.58  tff(c_135, plain, (![B_63, A_64]: (r2_hidden(B_63, A_64) | k1_xboole_0=A_64 | ~m1_subset_1(B_63, A_64))), inference(resolution, [status(thm)], [c_126, c_2])).
% 3.27/1.58  tff(c_12, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.27/1.58  tff(c_147, plain, (![A_67, C_68, B_69]: (m1_subset_1(A_67, C_68) | ~m1_subset_1(B_69, k1_zfmisc_1(C_68)) | ~r2_hidden(A_67, B_69))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.27/1.58  tff(c_168, plain, (![A_73, B_74, A_75]: (m1_subset_1(A_73, B_74) | ~r2_hidden(A_73, A_75) | ~r1_tarski(A_75, B_74))), inference(resolution, [status(thm)], [c_12, c_147])).
% 3.27/1.58  tff(c_171, plain, (![B_63, B_74, A_64]: (m1_subset_1(B_63, B_74) | ~r1_tarski(A_64, B_74) | k1_xboole_0=A_64 | ~m1_subset_1(B_63, A_64))), inference(resolution, [status(thm)], [c_135, c_168])).
% 3.27/1.58  tff(c_483, plain, (![B_63]: (m1_subset_1(B_63, '#skF_3') | k2_relat_1('#skF_4')=k1_xboole_0 | ~m1_subset_1(B_63, k2_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_481, c_171])).
% 3.27/1.58  tff(c_495, plain, (![B_115]: (m1_subset_1(B_115, '#skF_3') | ~m1_subset_1(B_115, k2_relat_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_86, c_483])).
% 3.27/1.58  tff(c_499, plain, (m1_subset_1('#skF_1'(k2_relat_1('#skF_4')), '#skF_3')), inference(resolution, [status(thm)], [c_6, c_495])).
% 3.27/1.58  tff(c_503, plain, $false, inference(negUnitSimplification, [status(thm)], [c_379, c_499])).
% 3.27/1.58  tff(c_504, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_146])).
% 3.27/1.58  tff(c_571, plain, (![A_124, B_125, C_126]: (k2_relset_1(A_124, B_125, C_126)=k2_relat_1(C_126) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.27/1.58  tff(c_582, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_571])).
% 3.27/1.58  tff(c_590, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_504, c_582])).
% 3.27/1.58  tff(c_592, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_590])).
% 3.27/1.58  tff(c_593, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_85])).
% 3.27/1.58  tff(c_801, plain, (![A_163, B_164, C_165]: (k1_relset_1(A_163, B_164, C_165)=k1_relat_1(C_165) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.27/1.58  tff(c_812, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_801])).
% 3.27/1.58  tff(c_820, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_593, c_812])).
% 3.27/1.58  tff(c_822, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_820])).
% 3.27/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.58  
% 3.27/1.58  Inference rules
% 3.27/1.58  ----------------------
% 3.27/1.58  #Ref     : 0
% 3.27/1.58  #Sup     : 160
% 3.27/1.58  #Fact    : 0
% 3.27/1.58  #Define  : 0
% 3.27/1.58  #Split   : 5
% 3.27/1.58  #Chain   : 0
% 3.27/1.58  #Close   : 0
% 3.27/1.58  
% 3.27/1.58  Ordering : KBO
% 3.27/1.58  
% 3.27/1.58  Simplification rules
% 3.27/1.58  ----------------------
% 3.27/1.58  #Subsume      : 9
% 3.27/1.58  #Demod        : 65
% 3.27/1.58  #Tautology    : 40
% 3.27/1.58  #SimpNegUnit  : 14
% 3.27/1.58  #BackRed      : 42
% 3.27/1.58  
% 3.27/1.58  #Partial instantiations: 0
% 3.27/1.58  #Strategies tried      : 1
% 3.27/1.58  
% 3.27/1.58  Timing (in seconds)
% 3.27/1.58  ----------------------
% 3.27/1.59  Preprocessing        : 0.34
% 3.27/1.59  Parsing              : 0.19
% 3.27/1.59  CNF conversion       : 0.02
% 3.27/1.59  Main loop            : 0.41
% 3.27/1.59  Inferencing          : 0.16
% 3.27/1.59  Reduction            : 0.12
% 3.27/1.59  Demodulation         : 0.08
% 3.27/1.59  BG Simplification    : 0.02
% 3.27/1.59  Subsumption          : 0.05
% 3.27/1.59  Abstraction          : 0.03
% 3.27/1.59  MUC search           : 0.00
% 3.27/1.59  Cooper               : 0.00
% 3.27/1.59  Total                : 0.79
% 3.27/1.59  Index Insertion      : 0.00
% 3.27/1.59  Index Deletion       : 0.00
% 3.27/1.59  Index Matching       : 0.00
% 3.27/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------

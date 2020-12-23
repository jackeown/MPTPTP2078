%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:07 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 111 expanded)
%              Number of leaves         :   35 (  51 expanded)
%              Depth                    :    7
%              Number of atoms          :   93 ( 168 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_336,plain,(
    ! [A_99,B_100,C_101] :
      ( k2_relset_1(A_99,B_100,C_101) = k2_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_345,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_336])).

tff(c_398,plain,(
    ! [A_112,B_113,C_114] :
      ( m1_subset_1(k2_relset_1(A_112,B_113,C_114),k1_zfmisc_1(B_113))
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_419,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_398])).

tff(c_426,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_419])).

tff(c_12,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_434,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_426,c_12])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,k2_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ! [A_20,B_21] : v1_relat_1(k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_50,plain,(
    ! [B_45,A_46] :
      ( v1_relat_1(B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_46))
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_56,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_50])).

tff(c_60,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_56])).

tff(c_116,plain,(
    ! [C_62,A_63,B_64] :
      ( v4_relat_1(C_62,A_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_125,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_116])).

tff(c_242,plain,(
    ! [B_84,A_85] :
      ( k7_relat_1(B_84,A_85) = B_84
      | ~ v4_relat_1(B_84,A_85)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_248,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_125,c_242])).

tff(c_252,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_248])).

tff(c_24,plain,(
    ! [B_25,A_24] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_25,A_24)),A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_285,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_24])).

tff(c_289,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_285])).

tff(c_6,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_137,plain,(
    ! [A_68,C_69,B_70] :
      ( r1_tarski(A_68,C_69)
      | ~ r1_tarski(B_70,C_69)
      | ~ r1_tarski(A_68,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_149,plain,(
    ! [A_68,A_7,B_8] :
      ( r1_tarski(A_68,k2_xboole_0(A_7,B_8))
      | ~ r1_tarski(A_68,A_7) ) ),
    inference(resolution,[status(thm)],[c_6,c_137])).

tff(c_18,plain,(
    ! [A_19] :
      ( k2_xboole_0(k1_relat_1(A_19),k2_relat_1(A_19)) = k3_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_253,plain,(
    ! [A_86,C_87,B_88] :
      ( r1_tarski(k2_xboole_0(A_86,C_87),B_88)
      | ~ r1_tarski(C_87,B_88)
      | ~ r1_tarski(A_86,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_950,plain,(
    ! [A_188,B_189] :
      ( r1_tarski(k3_relat_1(A_188),B_189)
      | ~ r1_tarski(k2_relat_1(A_188),B_189)
      | ~ r1_tarski(k1_relat_1(A_188),B_189)
      | ~ v1_relat_1(A_188) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_253])).

tff(c_34,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1004,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_950,c_34])).

tff(c_1026,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1004])).

tff(c_1033,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1026])).

tff(c_1039,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_149,c_1033])).

tff(c_1047,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_1039])).

tff(c_1048,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1026])).

tff(c_1058,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_1048])).

tff(c_1064,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_1058])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:45:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.58  
% 3.31/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.58  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.31/1.58  
% 3.31/1.58  %Foreground sorts:
% 3.31/1.58  
% 3.31/1.58  
% 3.31/1.58  %Background operators:
% 3.31/1.58  
% 3.31/1.58  
% 3.31/1.58  %Foreground operators:
% 3.31/1.58  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.31/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.31/1.58  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.31/1.58  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.31/1.58  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.31/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.31/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.31/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.31/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.31/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.31/1.58  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.31/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.31/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.31/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.31/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.58  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.31/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.31/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.31/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.31/1.58  
% 3.31/1.59  tff(f_91, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relset_1)).
% 3.31/1.59  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.31/1.59  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.31/1.59  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.31/1.59  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.31/1.59  tff(f_62, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.31/1.59  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.31/1.59  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.31/1.59  tff(f_68, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.31/1.59  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 3.31/1.59  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.31/1.59  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.31/1.59  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 3.31/1.59  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.31/1.59  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.31/1.59  tff(c_336, plain, (![A_99, B_100, C_101]: (k2_relset_1(A_99, B_100, C_101)=k2_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.31/1.59  tff(c_345, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_336])).
% 3.31/1.59  tff(c_398, plain, (![A_112, B_113, C_114]: (m1_subset_1(k2_relset_1(A_112, B_113, C_114), k1_zfmisc_1(B_113)) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.31/1.59  tff(c_419, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_345, c_398])).
% 3.31/1.59  tff(c_426, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_419])).
% 3.31/1.59  tff(c_12, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.31/1.59  tff(c_434, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_426, c_12])).
% 3.31/1.59  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, k2_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.31/1.59  tff(c_20, plain, (![A_20, B_21]: (v1_relat_1(k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.31/1.59  tff(c_50, plain, (![B_45, A_46]: (v1_relat_1(B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(A_46)) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.31/1.59  tff(c_56, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_50])).
% 3.31/1.59  tff(c_60, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_56])).
% 3.31/1.59  tff(c_116, plain, (![C_62, A_63, B_64]: (v4_relat_1(C_62, A_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.31/1.59  tff(c_125, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_116])).
% 3.31/1.59  tff(c_242, plain, (![B_84, A_85]: (k7_relat_1(B_84, A_85)=B_84 | ~v4_relat_1(B_84, A_85) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.31/1.59  tff(c_248, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_125, c_242])).
% 3.31/1.59  tff(c_252, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_248])).
% 3.31/1.59  tff(c_24, plain, (![B_25, A_24]: (r1_tarski(k1_relat_1(k7_relat_1(B_25, A_24)), A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.31/1.59  tff(c_285, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_252, c_24])).
% 3.31/1.59  tff(c_289, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_285])).
% 3.31/1.59  tff(c_6, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.31/1.59  tff(c_137, plain, (![A_68, C_69, B_70]: (r1_tarski(A_68, C_69) | ~r1_tarski(B_70, C_69) | ~r1_tarski(A_68, B_70))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.31/1.59  tff(c_149, plain, (![A_68, A_7, B_8]: (r1_tarski(A_68, k2_xboole_0(A_7, B_8)) | ~r1_tarski(A_68, A_7))), inference(resolution, [status(thm)], [c_6, c_137])).
% 3.31/1.59  tff(c_18, plain, (![A_19]: (k2_xboole_0(k1_relat_1(A_19), k2_relat_1(A_19))=k3_relat_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.31/1.59  tff(c_253, plain, (![A_86, C_87, B_88]: (r1_tarski(k2_xboole_0(A_86, C_87), B_88) | ~r1_tarski(C_87, B_88) | ~r1_tarski(A_86, B_88))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.31/1.59  tff(c_950, plain, (![A_188, B_189]: (r1_tarski(k3_relat_1(A_188), B_189) | ~r1_tarski(k2_relat_1(A_188), B_189) | ~r1_tarski(k1_relat_1(A_188), B_189) | ~v1_relat_1(A_188))), inference(superposition, [status(thm), theory('equality')], [c_18, c_253])).
% 3.31/1.59  tff(c_34, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.31/1.59  tff(c_1004, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_950, c_34])).
% 3.31/1.59  tff(c_1026, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1004])).
% 3.31/1.59  tff(c_1033, plain, (~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_1026])).
% 3.31/1.59  tff(c_1039, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_149, c_1033])).
% 3.31/1.59  tff(c_1047, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_289, c_1039])).
% 3.31/1.59  tff(c_1048, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_1026])).
% 3.31/1.59  tff(c_1058, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_2, c_1048])).
% 3.31/1.59  tff(c_1064, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_434, c_1058])).
% 3.31/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.59  
% 3.31/1.59  Inference rules
% 3.31/1.59  ----------------------
% 3.31/1.59  #Ref     : 0
% 3.31/1.59  #Sup     : 233
% 3.31/1.59  #Fact    : 0
% 3.31/1.59  #Define  : 0
% 3.31/1.59  #Split   : 10
% 3.31/1.59  #Chain   : 0
% 3.31/1.59  #Close   : 0
% 3.31/1.59  
% 3.31/1.59  Ordering : KBO
% 3.31/1.59  
% 3.31/1.59  Simplification rules
% 3.31/1.59  ----------------------
% 3.31/1.59  #Subsume      : 102
% 3.31/1.59  #Demod        : 27
% 3.31/1.59  #Tautology    : 19
% 3.31/1.59  #SimpNegUnit  : 23
% 3.31/1.59  #BackRed      : 4
% 3.31/1.59  
% 3.31/1.59  #Partial instantiations: 0
% 3.31/1.59  #Strategies tried      : 1
% 3.31/1.59  
% 3.31/1.59  Timing (in seconds)
% 3.31/1.59  ----------------------
% 3.31/1.60  Preprocessing        : 0.33
% 3.31/1.60  Parsing              : 0.18
% 3.31/1.60  CNF conversion       : 0.02
% 3.31/1.60  Main loop            : 0.45
% 3.31/1.60  Inferencing          : 0.16
% 3.31/1.60  Reduction            : 0.12
% 3.31/1.60  Demodulation         : 0.08
% 3.31/1.60  BG Simplification    : 0.02
% 3.31/1.60  Subsumption          : 0.11
% 3.31/1.60  Abstraction          : 0.02
% 3.31/1.60  MUC search           : 0.00
% 3.31/1.60  Cooper               : 0.00
% 3.31/1.60  Total                : 0.81
% 3.31/1.60  Index Insertion      : 0.00
% 3.31/1.60  Index Deletion       : 0.00
% 3.31/1.60  Index Matching       : 0.00
% 3.31/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------

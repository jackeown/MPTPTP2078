%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:05 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 147 expanded)
%              Number of leaves         :   38 (  70 expanded)
%              Depth                    :   10
%              Number of atoms          :  110 ( 316 expanded)
%              Number of equality atoms :   30 (  68 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_112,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_92,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r1_tarski(k7_relset_1(A,B,D,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_2)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_82,axiom,(
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

tff(c_18,plain,(
    ! [A_32,B_33] : v1_relat_1(k2_zfmisc_1(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_74,plain,(
    ! [B_56,A_57] :
      ( v1_relat_1(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57))
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_77,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_74])).

tff(c_80,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_77])).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_40,plain,(
    ! [A_46] :
      ( v1_funct_2(A_46,k1_relat_1(A_46),k2_relat_1(A_46))
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_38,plain,(
    ! [A_46] :
      ( m1_subset_1(A_46,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_46),k2_relat_1(A_46))))
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_240,plain,(
    ! [A_111,B_112,C_113,D_114] :
      ( k7_relset_1(A_111,B_112,C_113,D_114) = k9_relat_1(C_113,D_114)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_243,plain,(
    ! [A_46,D_114] :
      ( k7_relset_1(k1_relat_1(A_46),k2_relat_1(A_46),A_46,D_114) = k9_relat_1(A_46,D_114)
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(resolution,[status(thm)],[c_38,c_240])).

tff(c_337,plain,(
    ! [A_141,B_142,D_143,C_144] :
      ( r1_tarski(k7_relset_1(A_141,B_142,D_143,C_144),B_142)
      | ~ m1_subset_1(D_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142)))
      | ~ v1_funct_2(D_143,A_141,B_142)
      | ~ v1_funct_1(D_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_347,plain,(
    ! [A_146,C_147] :
      ( r1_tarski(k7_relset_1(k1_relat_1(A_146),k2_relat_1(A_146),A_146,C_147),k2_relat_1(A_146))
      | ~ v1_funct_2(A_146,k1_relat_1(A_146),k2_relat_1(A_146))
      | ~ v1_funct_1(A_146)
      | ~ v1_relat_1(A_146) ) ),
    inference(resolution,[status(thm)],[c_38,c_337])).

tff(c_351,plain,(
    ! [A_148,D_149] :
      ( r1_tarski(k9_relat_1(A_148,D_149),k2_relat_1(A_148))
      | ~ v1_funct_2(A_148,k1_relat_1(A_148),k2_relat_1(A_148))
      | ~ v1_funct_1(A_148)
      | ~ v1_relat_1(A_148)
      | ~ v1_funct_1(A_148)
      | ~ v1_relat_1(A_148) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_347])).

tff(c_355,plain,(
    ! [A_150,D_151] :
      ( r1_tarski(k9_relat_1(A_150,D_151),k2_relat_1(A_150))
      | ~ v1_funct_1(A_150)
      | ~ v1_relat_1(A_150) ) ),
    inference(resolution,[status(thm)],[c_40,c_351])).

tff(c_140,plain,(
    ! [B_79,A_80] :
      ( k1_tarski(k1_funct_1(B_79,A_80)) = k2_relat_1(B_79)
      | k1_tarski(A_80) != k1_relat_1(B_79)
      | ~ v1_funct_1(B_79)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_46,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_146,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_46])).

tff(c_152,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_54,c_146])).

tff(c_154,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_52,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_107,plain,(
    ! [A_67,B_68,C_69] :
      ( k1_relset_1(A_67,B_68,C_69) = k1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_115,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_107])).

tff(c_217,plain,(
    ! [B_108,A_109,C_110] :
      ( k1_xboole_0 = B_108
      | k1_relset_1(A_109,B_108,C_110) = A_109
      | ~ v1_funct_2(C_110,A_109,B_108)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_109,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_223,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_217])).

tff(c_227,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_115,c_223])).

tff(c_229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_48,c_227])).

tff(c_231,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_234,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_50])).

tff(c_24,plain,(
    ! [A_39,B_40,C_41,D_42] :
      ( k7_relset_1(A_39,B_40,C_41,D_42) = k9_relat_1(C_41,D_42)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_256,plain,(
    ! [D_42] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_42) = k9_relat_1('#skF_4',D_42) ),
    inference(resolution,[status(thm)],[c_234,c_24])).

tff(c_230,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_262,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_230])).

tff(c_269,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_262])).

tff(c_358,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_355,c_269])).

tff(c_362,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_54,c_358])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:39:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.39  
% 2.75/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.40  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.75/1.40  
% 2.75/1.40  %Foreground sorts:
% 2.75/1.40  
% 2.75/1.40  
% 2.75/1.40  %Background operators:
% 2.75/1.40  
% 2.75/1.40  
% 2.75/1.40  %Foreground operators:
% 2.75/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.75/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.75/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.75/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.75/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.75/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.75/1.40  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.75/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.75/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.75/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.75/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.75/1.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.75/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.75/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.75/1.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.75/1.40  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.75/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.75/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.75/1.40  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.75/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.75/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.75/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.75/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.75/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.75/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.75/1.40  
% 2.75/1.42  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.75/1.42  tff(f_112, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 2.75/1.42  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.75/1.42  tff(f_92, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 2.75/1.42  tff(f_64, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.75/1.42  tff(f_100, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k7_relset_1(A, B, D, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_funct_2)).
% 2.75/1.42  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 2.75/1.42  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.75/1.42  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.75/1.42  tff(c_18, plain, (![A_32, B_33]: (v1_relat_1(k2_zfmisc_1(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.75/1.42  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.75/1.42  tff(c_74, plain, (![B_56, A_57]: (v1_relat_1(B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.75/1.42  tff(c_77, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_50, c_74])).
% 2.75/1.42  tff(c_80, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_77])).
% 2.75/1.42  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.75/1.42  tff(c_40, plain, (![A_46]: (v1_funct_2(A_46, k1_relat_1(A_46), k2_relat_1(A_46)) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.75/1.42  tff(c_38, plain, (![A_46]: (m1_subset_1(A_46, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_46), k2_relat_1(A_46)))) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.75/1.42  tff(c_240, plain, (![A_111, B_112, C_113, D_114]: (k7_relset_1(A_111, B_112, C_113, D_114)=k9_relat_1(C_113, D_114) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.75/1.42  tff(c_243, plain, (![A_46, D_114]: (k7_relset_1(k1_relat_1(A_46), k2_relat_1(A_46), A_46, D_114)=k9_relat_1(A_46, D_114) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(resolution, [status(thm)], [c_38, c_240])).
% 2.75/1.42  tff(c_337, plain, (![A_141, B_142, D_143, C_144]: (r1_tarski(k7_relset_1(A_141, B_142, D_143, C_144), B_142) | ~m1_subset_1(D_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))) | ~v1_funct_2(D_143, A_141, B_142) | ~v1_funct_1(D_143))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.75/1.42  tff(c_347, plain, (![A_146, C_147]: (r1_tarski(k7_relset_1(k1_relat_1(A_146), k2_relat_1(A_146), A_146, C_147), k2_relat_1(A_146)) | ~v1_funct_2(A_146, k1_relat_1(A_146), k2_relat_1(A_146)) | ~v1_funct_1(A_146) | ~v1_relat_1(A_146))), inference(resolution, [status(thm)], [c_38, c_337])).
% 2.75/1.42  tff(c_351, plain, (![A_148, D_149]: (r1_tarski(k9_relat_1(A_148, D_149), k2_relat_1(A_148)) | ~v1_funct_2(A_148, k1_relat_1(A_148), k2_relat_1(A_148)) | ~v1_funct_1(A_148) | ~v1_relat_1(A_148) | ~v1_funct_1(A_148) | ~v1_relat_1(A_148))), inference(superposition, [status(thm), theory('equality')], [c_243, c_347])).
% 2.75/1.42  tff(c_355, plain, (![A_150, D_151]: (r1_tarski(k9_relat_1(A_150, D_151), k2_relat_1(A_150)) | ~v1_funct_1(A_150) | ~v1_relat_1(A_150))), inference(resolution, [status(thm)], [c_40, c_351])).
% 2.75/1.42  tff(c_140, plain, (![B_79, A_80]: (k1_tarski(k1_funct_1(B_79, A_80))=k2_relat_1(B_79) | k1_tarski(A_80)!=k1_relat_1(B_79) | ~v1_funct_1(B_79) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.75/1.42  tff(c_46, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.75/1.42  tff(c_146, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_140, c_46])).
% 2.75/1.42  tff(c_152, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_54, c_146])).
% 2.75/1.42  tff(c_154, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_152])).
% 2.75/1.42  tff(c_48, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.75/1.42  tff(c_52, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.75/1.42  tff(c_107, plain, (![A_67, B_68, C_69]: (k1_relset_1(A_67, B_68, C_69)=k1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.75/1.42  tff(c_115, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_107])).
% 2.75/1.42  tff(c_217, plain, (![B_108, A_109, C_110]: (k1_xboole_0=B_108 | k1_relset_1(A_109, B_108, C_110)=A_109 | ~v1_funct_2(C_110, A_109, B_108) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_109, B_108))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.75/1.42  tff(c_223, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_50, c_217])).
% 2.75/1.42  tff(c_227, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_115, c_223])).
% 2.75/1.42  tff(c_229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_154, c_48, c_227])).
% 2.75/1.42  tff(c_231, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_152])).
% 2.75/1.42  tff(c_234, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_50])).
% 2.75/1.42  tff(c_24, plain, (![A_39, B_40, C_41, D_42]: (k7_relset_1(A_39, B_40, C_41, D_42)=k9_relat_1(C_41, D_42) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.75/1.42  tff(c_256, plain, (![D_42]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_42)=k9_relat_1('#skF_4', D_42))), inference(resolution, [status(thm)], [c_234, c_24])).
% 2.75/1.42  tff(c_230, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_152])).
% 2.75/1.42  tff(c_262, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_230])).
% 2.75/1.42  tff(c_269, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_256, c_262])).
% 2.75/1.42  tff(c_358, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_355, c_269])).
% 2.75/1.42  tff(c_362, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_54, c_358])).
% 2.75/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.42  
% 2.75/1.42  Inference rules
% 2.75/1.42  ----------------------
% 2.75/1.42  #Ref     : 0
% 2.75/1.42  #Sup     : 63
% 2.75/1.42  #Fact    : 0
% 2.75/1.42  #Define  : 0
% 2.75/1.42  #Split   : 1
% 2.75/1.42  #Chain   : 0
% 2.75/1.42  #Close   : 0
% 2.75/1.42  
% 2.75/1.42  Ordering : KBO
% 2.75/1.42  
% 2.75/1.42  Simplification rules
% 2.75/1.42  ----------------------
% 2.75/1.42  #Subsume      : 9
% 2.75/1.42  #Demod        : 36
% 2.75/1.42  #Tautology    : 42
% 2.75/1.42  #SimpNegUnit  : 4
% 2.75/1.42  #BackRed      : 7
% 2.75/1.42  
% 2.75/1.42  #Partial instantiations: 0
% 2.75/1.42  #Strategies tried      : 1
% 2.75/1.42  
% 2.75/1.42  Timing (in seconds)
% 2.75/1.42  ----------------------
% 2.75/1.42  Preprocessing        : 0.37
% 2.75/1.42  Parsing              : 0.19
% 2.75/1.42  CNF conversion       : 0.02
% 2.75/1.42  Main loop            : 0.26
% 2.75/1.42  Inferencing          : 0.10
% 2.75/1.42  Reduction            : 0.08
% 2.75/1.42  Demodulation         : 0.06
% 2.75/1.42  BG Simplification    : 0.02
% 2.75/1.42  Subsumption          : 0.04
% 2.75/1.42  Abstraction          : 0.01
% 2.75/1.42  MUC search           : 0.00
% 2.75/1.42  Cooper               : 0.00
% 2.75/1.42  Total                : 0.68
% 2.75/1.42  Index Insertion      : 0.00
% 2.75/1.42  Index Deletion       : 0.00
% 2.75/1.42  Index Matching       : 0.00
% 2.75/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------

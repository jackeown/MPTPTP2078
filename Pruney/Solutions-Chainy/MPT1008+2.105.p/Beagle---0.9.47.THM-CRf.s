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
% DateTime   : Thu Dec  3 10:14:40 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 287 expanded)
%              Number of leaves         :   42 ( 120 expanded)
%              Depth                    :   13
%              Number of atoms          :  123 ( 679 expanded)
%              Number of equality atoms :   62 ( 306 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_54,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_122,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_98,axiom,(
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

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
        & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(c_30,plain,(
    ! [A_19,B_20] : v1_relat_1(k2_zfmisc_1(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_107,plain,(
    ! [B_51,A_52] :
      ( v1_relat_1(B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_52))
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_110,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_64,c_107])).

tff(c_113,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_110])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_66,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_153,plain,(
    ! [A_64,B_65,C_66] :
      ( k1_relset_1(A_64,B_65,C_66) = k1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_157,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_153])).

tff(c_189,plain,(
    ! [B_92,A_93,C_94] :
      ( k1_xboole_0 = B_92
      | k1_relset_1(A_93,B_92,C_94) = A_93
      | ~ v1_funct_2(C_94,A_93,B_92)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_192,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_189])).

tff(c_195,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_157,c_192])).

tff(c_196,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_195])).

tff(c_28,plain,(
    ! [A_16,B_18] :
      ( k9_relat_1(A_16,k1_tarski(B_18)) = k11_relat_1(A_16,B_18)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_287,plain,(
    ! [A_102] :
      ( k9_relat_1(A_102,k1_relat_1('#skF_5')) = k11_relat_1(A_102,'#skF_3')
      | ~ v1_relat_1(A_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_28])).

tff(c_32,plain,(
    ! [A_21] :
      ( k9_relat_1(A_21,k1_relat_1(A_21)) = k2_relat_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_294,plain,
    ( k11_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_32])).

tff(c_304,plain,(
    k11_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_113,c_294])).

tff(c_208,plain,(
    ! [A_16] :
      ( k9_relat_1(A_16,k1_relat_1('#skF_5')) = k11_relat_1(A_16,'#skF_3')
      | ~ v1_relat_1(A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_28])).

tff(c_162,plain,(
    ! [A_67,B_68,C_69,D_70] :
      ( k7_relset_1(A_67,B_68,C_69,D_70) = k9_relat_1(C_69,D_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_165,plain,(
    ! [D_70] : k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5',D_70) = k9_relat_1('#skF_5',D_70) ),
    inference(resolution,[status(thm)],[c_64,c_162])).

tff(c_197,plain,(
    ! [D_70] : k7_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5',D_70) = k9_relat_1('#skF_5',D_70) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_165])).

tff(c_68,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_201,plain,(
    v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_66])).

tff(c_200,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_64])).

tff(c_2673,plain,(
    ! [B_10184,A_10185,C_10186] :
      ( k1_xboole_0 = B_10184
      | k8_relset_1(A_10185,B_10184,C_10186,B_10184) = A_10185
      | ~ m1_subset_1(C_10186,k1_zfmisc_1(k2_zfmisc_1(A_10185,B_10184)))
      | ~ v1_funct_2(C_10186,A_10185,B_10184)
      | ~ v1_funct_1(C_10186) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2683,plain,
    ( k1_xboole_0 = '#skF_4'
    | k8_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5','#skF_4') = k1_relat_1('#skF_5')
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_200,c_2673])).

tff(c_2686,plain,
    ( k1_xboole_0 = '#skF_4'
    | k8_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5','#skF_4') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_201,c_2683])).

tff(c_2687,plain,(
    k8_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5','#skF_4') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2686])).

tff(c_283,plain,(
    ! [B_99,A_100,C_101] :
      ( k7_relset_1(B_99,A_100,C_101,k8_relset_1(B_99,A_100,C_101,A_100)) = k2_relset_1(B_99,A_100,C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(B_99,A_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_286,plain,(
    k7_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5',k8_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5','#skF_4')) = k2_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_200,c_283])).

tff(c_2689,plain,(
    k7_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5',k1_relat_1('#skF_5')) = k2_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2687,c_286])).

tff(c_2690,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5') = k9_relat_1('#skF_5',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_2689])).

tff(c_72,plain,(
    ! [A_46] : k2_tarski(A_46,A_46) = k1_tarski(A_46) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [D_6,A_1] : r2_hidden(D_6,k2_tarski(A_1,D_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_78,plain,(
    ! [A_46] : r2_hidden(A_46,k1_tarski(A_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_4])).

tff(c_211,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_78])).

tff(c_34,plain,(
    ! [B_23,A_22] :
      ( k1_tarski(k1_funct_1(B_23,A_22)) = k11_relat_1(B_23,A_22)
      | ~ r2_hidden(A_22,k1_relat_1(B_23))
      | ~ v1_funct_1(B_23)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_217,plain,
    ( k1_tarski(k1_funct_1('#skF_5','#skF_3')) = k11_relat_1('#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_211,c_34])).

tff(c_220,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_3')) = k11_relat_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_68,c_217])).

tff(c_60,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') != k1_tarski(k1_funct_1('#skF_5','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_199,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5') != k1_tarski(k1_funct_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_60])).

tff(c_254,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5') != k11_relat_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_199])).

tff(c_308,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),'#skF_4','#skF_5') != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_254])).

tff(c_2721,plain,(
    k9_relat_1('#skF_5',k1_relat_1('#skF_5')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2690,c_308])).

tff(c_2759,plain,
    ( k11_relat_1('#skF_5','#skF_3') != k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_2721])).

tff(c_2765,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_304,c_2759])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:56:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.80/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.67  
% 3.80/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.67  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 3.80/1.67  
% 3.80/1.67  %Foreground sorts:
% 3.80/1.67  
% 3.80/1.67  
% 3.80/1.67  %Background operators:
% 3.80/1.67  
% 3.80/1.67  
% 3.80/1.67  %Foreground operators:
% 3.80/1.67  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.80/1.67  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.80/1.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.80/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.80/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.80/1.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.80/1.67  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.80/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.80/1.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.80/1.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.80/1.67  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.80/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.80/1.67  tff('#skF_5', type, '#skF_5': $i).
% 3.80/1.67  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.80/1.67  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.80/1.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.80/1.67  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.80/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.80/1.67  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.80/1.67  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.80/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.80/1.67  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.80/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.80/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.80/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.80/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.80/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.80/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.80/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.80/1.67  
% 3.98/1.69  tff(f_54, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.98/1.69  tff(f_122, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 3.98/1.69  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.98/1.69  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.98/1.69  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.98/1.69  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 3.98/1.69  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 3.98/1.69  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.98/1.69  tff(f_110, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_2)).
% 3.98/1.69  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 3.98/1.69  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.98/1.69  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.98/1.69  tff(f_66, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 3.98/1.69  tff(c_30, plain, (![A_19, B_20]: (v1_relat_1(k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.98/1.69  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.98/1.69  tff(c_107, plain, (![B_51, A_52]: (v1_relat_1(B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(A_52)) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.98/1.69  tff(c_110, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_64, c_107])).
% 3.98/1.69  tff(c_113, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_110])).
% 3.98/1.69  tff(c_62, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.98/1.69  tff(c_66, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.98/1.69  tff(c_153, plain, (![A_64, B_65, C_66]: (k1_relset_1(A_64, B_65, C_66)=k1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.98/1.69  tff(c_157, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_153])).
% 3.98/1.69  tff(c_189, plain, (![B_92, A_93, C_94]: (k1_xboole_0=B_92 | k1_relset_1(A_93, B_92, C_94)=A_93 | ~v1_funct_2(C_94, A_93, B_92) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.98/1.69  tff(c_192, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_64, c_189])).
% 3.98/1.69  tff(c_195, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_157, c_192])).
% 3.98/1.69  tff(c_196, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_195])).
% 3.98/1.69  tff(c_28, plain, (![A_16, B_18]: (k9_relat_1(A_16, k1_tarski(B_18))=k11_relat_1(A_16, B_18) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.98/1.69  tff(c_287, plain, (![A_102]: (k9_relat_1(A_102, k1_relat_1('#skF_5'))=k11_relat_1(A_102, '#skF_3') | ~v1_relat_1(A_102))), inference(superposition, [status(thm), theory('equality')], [c_196, c_28])).
% 3.98/1.69  tff(c_32, plain, (![A_21]: (k9_relat_1(A_21, k1_relat_1(A_21))=k2_relat_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.98/1.69  tff(c_294, plain, (k11_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_287, c_32])).
% 3.98/1.69  tff(c_304, plain, (k11_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_113, c_294])).
% 3.98/1.69  tff(c_208, plain, (![A_16]: (k9_relat_1(A_16, k1_relat_1('#skF_5'))=k11_relat_1(A_16, '#skF_3') | ~v1_relat_1(A_16))), inference(superposition, [status(thm), theory('equality')], [c_196, c_28])).
% 3.98/1.69  tff(c_162, plain, (![A_67, B_68, C_69, D_70]: (k7_relset_1(A_67, B_68, C_69, D_70)=k9_relat_1(C_69, D_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.98/1.69  tff(c_165, plain, (![D_70]: (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5', D_70)=k9_relat_1('#skF_5', D_70))), inference(resolution, [status(thm)], [c_64, c_162])).
% 3.98/1.69  tff(c_197, plain, (![D_70]: (k7_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5', D_70)=k9_relat_1('#skF_5', D_70))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_165])).
% 3.98/1.69  tff(c_68, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.98/1.69  tff(c_201, plain, (v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_66])).
% 3.98/1.69  tff(c_200, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_64])).
% 3.98/1.69  tff(c_2673, plain, (![B_10184, A_10185, C_10186]: (k1_xboole_0=B_10184 | k8_relset_1(A_10185, B_10184, C_10186, B_10184)=A_10185 | ~m1_subset_1(C_10186, k1_zfmisc_1(k2_zfmisc_1(A_10185, B_10184))) | ~v1_funct_2(C_10186, A_10185, B_10184) | ~v1_funct_1(C_10186))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.98/1.69  tff(c_2683, plain, (k1_xboole_0='#skF_4' | k8_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5', '#skF_4')=k1_relat_1('#skF_5') | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_200, c_2673])).
% 3.98/1.69  tff(c_2686, plain, (k1_xboole_0='#skF_4' | k8_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5', '#skF_4')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_201, c_2683])).
% 3.98/1.69  tff(c_2687, plain, (k8_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5', '#skF_4')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_2686])).
% 3.98/1.69  tff(c_283, plain, (![B_99, A_100, C_101]: (k7_relset_1(B_99, A_100, C_101, k8_relset_1(B_99, A_100, C_101, A_100))=k2_relset_1(B_99, A_100, C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(B_99, A_100))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.98/1.69  tff(c_286, plain, (k7_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5', k8_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5', '#skF_4'))=k2_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_200, c_283])).
% 3.98/1.69  tff(c_2689, plain, (k7_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5', k1_relat_1('#skF_5'))=k2_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2687, c_286])).
% 3.98/1.69  tff(c_2690, plain, (k2_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5')=k9_relat_1('#skF_5', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_197, c_2689])).
% 3.98/1.69  tff(c_72, plain, (![A_46]: (k2_tarski(A_46, A_46)=k1_tarski(A_46))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.98/1.69  tff(c_4, plain, (![D_6, A_1]: (r2_hidden(D_6, k2_tarski(A_1, D_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.98/1.69  tff(c_78, plain, (![A_46]: (r2_hidden(A_46, k1_tarski(A_46)))), inference(superposition, [status(thm), theory('equality')], [c_72, c_4])).
% 3.98/1.69  tff(c_211, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_196, c_78])).
% 3.98/1.69  tff(c_34, plain, (![B_23, A_22]: (k1_tarski(k1_funct_1(B_23, A_22))=k11_relat_1(B_23, A_22) | ~r2_hidden(A_22, k1_relat_1(B_23)) | ~v1_funct_1(B_23) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.98/1.69  tff(c_217, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))=k11_relat_1('#skF_5', '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_211, c_34])).
% 3.98/1.69  tff(c_220, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))=k11_relat_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_68, c_217])).
% 3.98/1.69  tff(c_60, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')!=k1_tarski(k1_funct_1('#skF_5', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.98/1.69  tff(c_199, plain, (k2_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5')!=k1_tarski(k1_funct_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_60])).
% 3.98/1.69  tff(c_254, plain, (k2_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5')!=k11_relat_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_220, c_199])).
% 3.98/1.69  tff(c_308, plain, (k2_relset_1(k1_relat_1('#skF_5'), '#skF_4', '#skF_5')!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_304, c_254])).
% 3.98/1.69  tff(c_2721, plain, (k9_relat_1('#skF_5', k1_relat_1('#skF_5'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2690, c_308])).
% 3.98/1.69  tff(c_2759, plain, (k11_relat_1('#skF_5', '#skF_3')!=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_208, c_2721])).
% 3.98/1.69  tff(c_2765, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_113, c_304, c_2759])).
% 3.98/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.69  
% 3.98/1.69  Inference rules
% 3.98/1.69  ----------------------
% 3.98/1.69  #Ref     : 0
% 3.98/1.69  #Sup     : 311
% 3.98/1.69  #Fact    : 4
% 3.98/1.69  #Define  : 0
% 3.98/1.69  #Split   : 4
% 3.98/1.69  #Chain   : 0
% 3.98/1.69  #Close   : 0
% 3.98/1.69  
% 3.98/1.69  Ordering : KBO
% 3.98/1.69  
% 3.98/1.69  Simplification rules
% 3.98/1.69  ----------------------
% 3.98/1.69  #Subsume      : 93
% 3.98/1.69  #Demod        : 97
% 3.98/1.69  #Tautology    : 104
% 3.98/1.69  #SimpNegUnit  : 5
% 3.98/1.69  #BackRed      : 12
% 3.98/1.69  
% 3.98/1.69  #Partial instantiations: 4550
% 3.98/1.69  #Strategies tried      : 1
% 3.98/1.69  
% 3.98/1.69  Timing (in seconds)
% 3.98/1.69  ----------------------
% 3.98/1.69  Preprocessing        : 0.33
% 3.98/1.69  Parsing              : 0.16
% 3.98/1.69  CNF conversion       : 0.02
% 3.98/1.69  Main loop            : 0.56
% 3.98/1.69  Inferencing          : 0.31
% 3.98/1.69  Reduction            : 0.13
% 3.98/1.69  Demodulation         : 0.09
% 3.98/1.69  BG Simplification    : 0.03
% 3.98/1.69  Subsumption          : 0.07
% 3.98/1.69  Abstraction          : 0.02
% 3.98/1.69  MUC search           : 0.00
% 3.98/1.69  Cooper               : 0.00
% 3.98/1.69  Total                : 0.92
% 3.98/1.69  Index Insertion      : 0.00
% 3.98/1.69  Index Deletion       : 0.00
% 3.98/1.69  Index Matching       : 0.00
% 3.98/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------

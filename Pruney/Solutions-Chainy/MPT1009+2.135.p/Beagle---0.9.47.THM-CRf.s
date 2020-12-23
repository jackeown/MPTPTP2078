%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:01 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 173 expanded)
%              Number of leaves         :   44 (  80 expanded)
%              Depth                    :   12
%              Number of atoms          :  113 ( 329 expanded)
%              Number of equality atoms :   43 (  83 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_116,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_104,axiom,(
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

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_22,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_87,plain,(
    ! [B_46,A_47] :
      ( v1_relat_1(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_90,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_87])).

tff(c_93,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_90])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_58,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_173,plain,(
    ! [A_66,B_67,C_68] :
      ( k1_relset_1(A_66,B_67,C_68) = k1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_177,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_173])).

tff(c_248,plain,(
    ! [B_93,A_94,C_95] :
      ( k1_xboole_0 = B_93
      | k1_relset_1(A_94,B_93,C_95) = A_94
      | ~ v1_funct_2(C_95,A_94,B_93)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_94,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_251,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_6',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_248])).

tff(c_254,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_177,c_251])).

tff(c_255,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_254])).

tff(c_118,plain,(
    ! [C_57,A_58,B_59] :
      ( v4_relat_1(C_57,A_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_122,plain,(
    v4_relat_1('#skF_6',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_118])).

tff(c_260,plain,(
    v4_relat_1('#skF_6',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_122])).

tff(c_28,plain,(
    ! [B_22,A_21] :
      ( k7_relat_1(B_22,A_21) = B_22
      | ~ v4_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_290,plain,
    ( k7_relat_1('#skF_6',k1_relat_1('#skF_6')) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_260,c_28])).

tff(c_293,plain,(
    k7_relat_1('#skF_6',k1_relat_1('#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_290])).

tff(c_26,plain,(
    ! [B_20,A_19] :
      ( k2_relat_1(k7_relat_1(B_20,A_19)) = k9_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_304,plain,
    ( k9_relat_1('#skF_6',k1_relat_1('#skF_6')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_26])).

tff(c_308,plain,(
    k9_relat_1('#skF_6',k1_relat_1('#skF_6')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_304])).

tff(c_24,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k9_relat_1(B_18,A_17),k9_relat_1(B_18,k1_relat_1(B_18)))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_373,plain,(
    ! [A_17] :
      ( r1_tarski(k9_relat_1('#skF_6',A_17),k2_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_24])).

tff(c_381,plain,(
    ! [A_17] : r1_tarski(k9_relat_1('#skF_6',A_17),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_373])).

tff(c_60,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_125,plain,
    ( k7_relat_1('#skF_6',k1_tarski('#skF_3')) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_122,c_28])).

tff(c_128,plain,(
    k7_relat_1('#skF_6',k1_tarski('#skF_3')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_125])).

tff(c_132,plain,
    ( k9_relat_1('#skF_6',k1_tarski('#skF_3')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_26])).

tff(c_136,plain,(
    k9_relat_1('#skF_6',k1_tarski('#skF_3')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_132])).

tff(c_20,plain,(
    ! [A_12,B_14] :
      ( k9_relat_1(A_12,k1_tarski(B_14)) = k11_relat_1(A_12,B_14)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_141,plain,
    ( k11_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_20])).

tff(c_148,plain,(
    k11_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_141])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_281,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_4])).

tff(c_30,plain,(
    ! [B_24,A_23] :
      ( k1_tarski(k1_funct_1(B_24,A_23)) = k11_relat_1(B_24,A_23)
      | ~ r2_hidden(A_23,k1_relat_1(B_24))
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_297,plain,
    ( k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k11_relat_1('#skF_6','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_281,c_30])).

tff(c_300,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_60,c_148,c_297])).

tff(c_197,plain,(
    ! [A_78,B_79,C_80,D_81] :
      ( k7_relset_1(A_78,B_79,C_80,D_81) = k9_relat_1(C_80,D_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_200,plain,(
    ! [D_81] : k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6',D_81) = k9_relat_1('#skF_6',D_81) ),
    inference(resolution,[status(thm)],[c_56,c_197])).

tff(c_52,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_212,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_52])).

tff(c_399,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_212])).

tff(c_402,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_399])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n023.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:50:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.31  
% 2.19/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.31  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.19/1.31  
% 2.19/1.31  %Foreground sorts:
% 2.19/1.31  
% 2.19/1.31  
% 2.19/1.31  %Background operators:
% 2.19/1.31  
% 2.19/1.31  
% 2.19/1.31  %Foreground operators:
% 2.19/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.19/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.19/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.19/1.31  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.19/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.19/1.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.19/1.31  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.19/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.19/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.19/1.31  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.19/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.31  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.19/1.31  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.19/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.31  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.19/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.19/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.19/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.19/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.19/1.31  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.19/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.19/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.19/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.31  
% 2.19/1.33  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.19/1.33  tff(f_116, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 2.19/1.33  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.19/1.33  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.19/1.33  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.19/1.33  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.19/1.33  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.19/1.33  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.19/1.33  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k9_relat_1(B, k1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_relat_1)).
% 2.19/1.33  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.19/1.33  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.19/1.33  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 2.19/1.33  tff(f_86, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.19/1.33  tff(c_22, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.19/1.33  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.19/1.33  tff(c_87, plain, (![B_46, A_47]: (v1_relat_1(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.19/1.33  tff(c_90, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_56, c_87])).
% 2.19/1.33  tff(c_93, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_90])).
% 2.19/1.33  tff(c_54, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.19/1.33  tff(c_58, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.19/1.33  tff(c_173, plain, (![A_66, B_67, C_68]: (k1_relset_1(A_66, B_67, C_68)=k1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.19/1.33  tff(c_177, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_173])).
% 2.19/1.33  tff(c_248, plain, (![B_93, A_94, C_95]: (k1_xboole_0=B_93 | k1_relset_1(A_94, B_93, C_95)=A_94 | ~v1_funct_2(C_95, A_94, B_93) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_94, B_93))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.19/1.33  tff(c_251, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_6', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_56, c_248])).
% 2.19/1.33  tff(c_254, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_177, c_251])).
% 2.19/1.33  tff(c_255, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_54, c_254])).
% 2.19/1.33  tff(c_118, plain, (![C_57, A_58, B_59]: (v4_relat_1(C_57, A_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.19/1.33  tff(c_122, plain, (v4_relat_1('#skF_6', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_56, c_118])).
% 2.19/1.33  tff(c_260, plain, (v4_relat_1('#skF_6', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_255, c_122])).
% 2.19/1.33  tff(c_28, plain, (![B_22, A_21]: (k7_relat_1(B_22, A_21)=B_22 | ~v4_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.19/1.33  tff(c_290, plain, (k7_relat_1('#skF_6', k1_relat_1('#skF_6'))='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_260, c_28])).
% 2.19/1.33  tff(c_293, plain, (k7_relat_1('#skF_6', k1_relat_1('#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_93, c_290])).
% 2.19/1.33  tff(c_26, plain, (![B_20, A_19]: (k2_relat_1(k7_relat_1(B_20, A_19))=k9_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.19/1.33  tff(c_304, plain, (k9_relat_1('#skF_6', k1_relat_1('#skF_6'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_293, c_26])).
% 2.19/1.33  tff(c_308, plain, (k9_relat_1('#skF_6', k1_relat_1('#skF_6'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_304])).
% 2.19/1.33  tff(c_24, plain, (![B_18, A_17]: (r1_tarski(k9_relat_1(B_18, A_17), k9_relat_1(B_18, k1_relat_1(B_18))) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.19/1.33  tff(c_373, plain, (![A_17]: (r1_tarski(k9_relat_1('#skF_6', A_17), k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_308, c_24])).
% 2.19/1.33  tff(c_381, plain, (![A_17]: (r1_tarski(k9_relat_1('#skF_6', A_17), k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_373])).
% 2.19/1.33  tff(c_60, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.19/1.33  tff(c_125, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_3'))='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_122, c_28])).
% 2.19/1.33  tff(c_128, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_3'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_93, c_125])).
% 2.19/1.33  tff(c_132, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_3'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_128, c_26])).
% 2.19/1.33  tff(c_136, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_3'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_132])).
% 2.19/1.33  tff(c_20, plain, (![A_12, B_14]: (k9_relat_1(A_12, k1_tarski(B_14))=k11_relat_1(A_12, B_14) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.19/1.33  tff(c_141, plain, (k11_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_136, c_20])).
% 2.19/1.33  tff(c_148, plain, (k11_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_141])).
% 2.19/1.33  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.19/1.33  tff(c_281, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_255, c_4])).
% 2.19/1.33  tff(c_30, plain, (![B_24, A_23]: (k1_tarski(k1_funct_1(B_24, A_23))=k11_relat_1(B_24, A_23) | ~r2_hidden(A_23, k1_relat_1(B_24)) | ~v1_funct_1(B_24) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.19/1.33  tff(c_297, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k11_relat_1('#skF_6', '#skF_3') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_281, c_30])).
% 2.19/1.33  tff(c_300, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_60, c_148, c_297])).
% 2.19/1.33  tff(c_197, plain, (![A_78, B_79, C_80, D_81]: (k7_relset_1(A_78, B_79, C_80, D_81)=k9_relat_1(C_80, D_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.19/1.33  tff(c_200, plain, (![D_81]: (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', D_81)=k9_relat_1('#skF_6', D_81))), inference(resolution, [status(thm)], [c_56, c_197])).
% 2.19/1.33  tff(c_52, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.19/1.33  tff(c_212, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_52])).
% 2.19/1.33  tff(c_399, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_300, c_212])).
% 2.19/1.33  tff(c_402, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_381, c_399])).
% 2.19/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.33  
% 2.19/1.33  Inference rules
% 2.19/1.33  ----------------------
% 2.19/1.33  #Ref     : 0
% 2.19/1.33  #Sup     : 73
% 2.19/1.33  #Fact    : 0
% 2.19/1.33  #Define  : 0
% 2.19/1.33  #Split   : 0
% 2.19/1.33  #Chain   : 0
% 2.19/1.33  #Close   : 0
% 2.19/1.33  
% 2.19/1.33  Ordering : KBO
% 2.19/1.33  
% 2.19/1.33  Simplification rules
% 2.19/1.33  ----------------------
% 2.19/1.33  #Subsume      : 0
% 2.19/1.33  #Demod        : 54
% 2.19/1.33  #Tautology    : 43
% 2.19/1.33  #SimpNegUnit  : 3
% 2.19/1.33  #BackRed      : 10
% 2.19/1.33  
% 2.19/1.33  #Partial instantiations: 0
% 2.19/1.33  #Strategies tried      : 1
% 2.19/1.33  
% 2.19/1.33  Timing (in seconds)
% 2.61/1.33  ----------------------
% 2.61/1.33  Preprocessing        : 0.33
% 2.61/1.33  Parsing              : 0.18
% 2.61/1.33  CNF conversion       : 0.02
% 2.61/1.33  Main loop            : 0.23
% 2.61/1.33  Inferencing          : 0.09
% 2.61/1.33  Reduction            : 0.07
% 2.61/1.33  Demodulation         : 0.05
% 2.61/1.33  BG Simplification    : 0.02
% 2.61/1.33  Subsumption          : 0.04
% 2.61/1.33  Abstraction          : 0.01
% 2.61/1.33  MUC search           : 0.00
% 2.61/1.33  Cooper               : 0.00
% 2.61/1.33  Total                : 0.60
% 2.61/1.33  Index Insertion      : 0.00
% 2.61/1.33  Index Deletion       : 0.00
% 2.61/1.33  Index Matching       : 0.00
% 2.61/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------

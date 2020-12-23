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
% DateTime   : Thu Dec  3 10:14:21 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 134 expanded)
%              Number of leaves         :   41 (  64 expanded)
%              Depth                    :    9
%              Number of atoms          :  136 ( 266 expanded)
%              Number of equality atoms :   35 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_60,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_126,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_114,axiom,(
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

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_30,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_96,plain,(
    ! [B_50,A_51] :
      ( v1_relat_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_99,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_62,c_96])).

tff(c_102,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_99])).

tff(c_66,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_613,plain,(
    ! [B_151,A_152] :
      ( r2_hidden(k1_funct_1(B_151,A_152),k2_relat_1(B_151))
      | ~ r2_hidden(A_152,k1_relat_1(B_151))
      | ~ v1_funct_1(B_151)
      | ~ v1_relat_1(B_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_114,plain,(
    ! [C_57,B_58,A_59] :
      ( v5_relat_1(C_57,B_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_59,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_118,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_114])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_64,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_165,plain,(
    ! [A_74,B_75,C_76] :
      ( k1_relset_1(A_74,B_75,C_76) = k1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_169,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_165])).

tff(c_283,plain,(
    ! [B_110,A_111,C_112] :
      ( k1_xboole_0 = B_110
      | k1_relset_1(A_111,B_110,C_112) = A_111
      | ~ v1_funct_2(C_112,A_111,B_110)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_111,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_290,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_283])).

tff(c_294,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_169,c_290])).

tff(c_295,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_294])).

tff(c_70,plain,(
    ! [A_46] : k2_tarski(A_46,A_46) = k1_tarski(A_46) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6,plain,(
    ! [D_6,B_2] : r2_hidden(D_6,k2_tarski(D_6,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_76,plain,(
    ! [A_46] : r2_hidden(A_46,k1_tarski(A_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_6])).

tff(c_311,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_76])).

tff(c_34,plain,(
    ! [C_24,B_23,A_22] :
      ( m1_subset_1(k1_funct_1(C_24,B_23),A_22)
      | ~ r2_hidden(B_23,k1_relat_1(C_24))
      | ~ v1_funct_1(C_24)
      | ~ v5_relat_1(C_24,A_22)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_317,plain,(
    ! [A_22] :
      ( m1_subset_1(k1_funct_1('#skF_5','#skF_3'),A_22)
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_22)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_311,c_34])).

tff(c_402,plain,(
    ! [A_117] :
      ( m1_subset_1(k1_funct_1('#skF_5','#skF_3'),A_117)
      | ~ v5_relat_1('#skF_5',A_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_66,c_317])).

tff(c_103,plain,(
    ! [A_52,B_53] :
      ( r2_hidden(A_52,B_53)
      | v1_xboole_0(B_53)
      | ~ m1_subset_1(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_58,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_107,plain,
    ( v1_xboole_0('#skF_4')
    | ~ m1_subset_1(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_103,c_58])).

tff(c_112,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_453,plain,(
    ~ v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_402,c_112])).

tff(c_476,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_453])).

tff(c_477,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_530,plain,(
    ! [A_134,B_135,C_136] :
      ( k2_relset_1(A_134,B_135,C_136) = k2_relat_1(C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_534,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_530])).

tff(c_540,plain,(
    ! [A_138,B_139,C_140] :
      ( m1_subset_1(k2_relset_1(A_138,B_139,C_140),k1_zfmisc_1(B_139))
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_564,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_534,c_540])).

tff(c_572,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_564])).

tff(c_26,plain,(
    ! [C_14,B_13,A_12] :
      ( ~ v1_xboole_0(C_14)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(C_14))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_574,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_12,k2_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_572,c_26])).

tff(c_580,plain,(
    ! [A_12] : ~ r2_hidden(A_12,k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_574])).

tff(c_617,plain,(
    ! [A_152] :
      ( ~ r2_hidden(A_152,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_613,c_580])).

tff(c_620,plain,(
    ! [A_152] : ~ r2_hidden(A_152,k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_66,c_617])).

tff(c_521,plain,(
    ! [A_131,B_132,C_133] :
      ( k1_relset_1(A_131,B_132,C_133) = k1_relat_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_525,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_521])).

tff(c_673,plain,(
    ! [B_175,A_176,C_177] :
      ( k1_xboole_0 = B_175
      | k1_relset_1(A_176,B_175,C_177) = A_176
      | ~ v1_funct_2(C_177,A_176,B_175)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(A_176,B_175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_680,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_673])).

tff(c_684,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_525,c_680])).

tff(c_685,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_684])).

tff(c_701,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_685,c_76])).

tff(c_706,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_620,c_701])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:05:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.39  
% 2.87/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.39  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 2.87/1.39  
% 2.87/1.39  %Foreground sorts:
% 2.87/1.39  
% 2.87/1.39  
% 2.87/1.39  %Background operators:
% 2.87/1.39  
% 2.87/1.39  
% 2.87/1.39  %Foreground operators:
% 2.87/1.39  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.87/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.87/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.87/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.87/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.87/1.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.87/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.87/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.87/1.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.87/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.87/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.87/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.87/1.39  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.87/1.39  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.87/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.87/1.39  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.87/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.87/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.87/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.87/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.39  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.87/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.87/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.87/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.87/1.39  
% 2.87/1.41  tff(f_60, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.87/1.41  tff(f_126, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 2.87/1.41  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.87/1.41  tff(f_68, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 2.87/1.41  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.87/1.41  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.87/1.41  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.87/1.41  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.87/1.41  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.87/1.41  tff(f_78, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_1)).
% 2.87/1.41  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.87/1.41  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.87/1.41  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.87/1.41  tff(f_51, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.87/1.41  tff(c_30, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.87/1.41  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.87/1.41  tff(c_96, plain, (![B_50, A_51]: (v1_relat_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.87/1.41  tff(c_99, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_96])).
% 2.87/1.41  tff(c_102, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_99])).
% 2.87/1.41  tff(c_66, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.87/1.41  tff(c_613, plain, (![B_151, A_152]: (r2_hidden(k1_funct_1(B_151, A_152), k2_relat_1(B_151)) | ~r2_hidden(A_152, k1_relat_1(B_151)) | ~v1_funct_1(B_151) | ~v1_relat_1(B_151))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.87/1.41  tff(c_114, plain, (![C_57, B_58, A_59]: (v5_relat_1(C_57, B_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_59, B_58))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.87/1.41  tff(c_118, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_62, c_114])).
% 2.87/1.41  tff(c_60, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.87/1.41  tff(c_64, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.87/1.41  tff(c_165, plain, (![A_74, B_75, C_76]: (k1_relset_1(A_74, B_75, C_76)=k1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.87/1.41  tff(c_169, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_165])).
% 2.87/1.41  tff(c_283, plain, (![B_110, A_111, C_112]: (k1_xboole_0=B_110 | k1_relset_1(A_111, B_110, C_112)=A_111 | ~v1_funct_2(C_112, A_111, B_110) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_111, B_110))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.87/1.41  tff(c_290, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_62, c_283])).
% 2.87/1.41  tff(c_294, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_169, c_290])).
% 2.87/1.41  tff(c_295, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_60, c_294])).
% 2.87/1.41  tff(c_70, plain, (![A_46]: (k2_tarski(A_46, A_46)=k1_tarski(A_46))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.87/1.41  tff(c_6, plain, (![D_6, B_2]: (r2_hidden(D_6, k2_tarski(D_6, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.87/1.41  tff(c_76, plain, (![A_46]: (r2_hidden(A_46, k1_tarski(A_46)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_6])).
% 2.87/1.41  tff(c_311, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_295, c_76])).
% 2.87/1.41  tff(c_34, plain, (![C_24, B_23, A_22]: (m1_subset_1(k1_funct_1(C_24, B_23), A_22) | ~r2_hidden(B_23, k1_relat_1(C_24)) | ~v1_funct_1(C_24) | ~v5_relat_1(C_24, A_22) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.87/1.41  tff(c_317, plain, (![A_22]: (m1_subset_1(k1_funct_1('#skF_5', '#skF_3'), A_22) | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_22) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_311, c_34])).
% 2.87/1.41  tff(c_402, plain, (![A_117]: (m1_subset_1(k1_funct_1('#skF_5', '#skF_3'), A_117) | ~v5_relat_1('#skF_5', A_117))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_66, c_317])).
% 2.87/1.41  tff(c_103, plain, (![A_52, B_53]: (r2_hidden(A_52, B_53) | v1_xboole_0(B_53) | ~m1_subset_1(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.87/1.41  tff(c_58, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.87/1.41  tff(c_107, plain, (v1_xboole_0('#skF_4') | ~m1_subset_1(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_103, c_58])).
% 2.87/1.41  tff(c_112, plain, (~m1_subset_1(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_107])).
% 2.87/1.41  tff(c_453, plain, (~v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_402, c_112])).
% 2.87/1.41  tff(c_476, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_453])).
% 2.87/1.41  tff(c_477, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_107])).
% 2.87/1.41  tff(c_530, plain, (![A_134, B_135, C_136]: (k2_relset_1(A_134, B_135, C_136)=k2_relat_1(C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.87/1.41  tff(c_534, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_530])).
% 2.87/1.41  tff(c_540, plain, (![A_138, B_139, C_140]: (m1_subset_1(k2_relset_1(A_138, B_139, C_140), k1_zfmisc_1(B_139)) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.87/1.41  tff(c_564, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_534, c_540])).
% 2.87/1.41  tff(c_572, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_564])).
% 2.87/1.41  tff(c_26, plain, (![C_14, B_13, A_12]: (~v1_xboole_0(C_14) | ~m1_subset_1(B_13, k1_zfmisc_1(C_14)) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.87/1.41  tff(c_574, plain, (![A_12]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_12, k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_572, c_26])).
% 2.87/1.41  tff(c_580, plain, (![A_12]: (~r2_hidden(A_12, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_477, c_574])).
% 2.87/1.41  tff(c_617, plain, (![A_152]: (~r2_hidden(A_152, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_613, c_580])).
% 2.87/1.41  tff(c_620, plain, (![A_152]: (~r2_hidden(A_152, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_66, c_617])).
% 2.87/1.41  tff(c_521, plain, (![A_131, B_132, C_133]: (k1_relset_1(A_131, B_132, C_133)=k1_relat_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.87/1.41  tff(c_525, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_521])).
% 2.87/1.41  tff(c_673, plain, (![B_175, A_176, C_177]: (k1_xboole_0=B_175 | k1_relset_1(A_176, B_175, C_177)=A_176 | ~v1_funct_2(C_177, A_176, B_175) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(A_176, B_175))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.87/1.41  tff(c_680, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_62, c_673])).
% 2.87/1.41  tff(c_684, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_525, c_680])).
% 2.87/1.41  tff(c_685, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_60, c_684])).
% 2.87/1.41  tff(c_701, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_685, c_76])).
% 2.87/1.41  tff(c_706, plain, $false, inference(negUnitSimplification, [status(thm)], [c_620, c_701])).
% 2.87/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.41  
% 2.87/1.41  Inference rules
% 2.87/1.41  ----------------------
% 2.87/1.41  #Ref     : 0
% 2.87/1.41  #Sup     : 130
% 2.87/1.41  #Fact    : 0
% 2.87/1.41  #Define  : 0
% 2.87/1.41  #Split   : 8
% 2.87/1.41  #Chain   : 0
% 2.87/1.41  #Close   : 0
% 2.87/1.41  
% 2.87/1.41  Ordering : KBO
% 2.87/1.41  
% 2.87/1.41  Simplification rules
% 2.87/1.41  ----------------------
% 2.87/1.41  #Subsume      : 11
% 2.87/1.41  #Demod        : 48
% 2.87/1.41  #Tautology    : 35
% 2.87/1.41  #SimpNegUnit  : 5
% 2.87/1.41  #BackRed      : 12
% 2.87/1.41  
% 2.87/1.41  #Partial instantiations: 0
% 2.87/1.41  #Strategies tried      : 1
% 2.87/1.41  
% 2.87/1.41  Timing (in seconds)
% 2.87/1.41  ----------------------
% 2.87/1.41  Preprocessing        : 0.33
% 2.87/1.41  Parsing              : 0.17
% 2.87/1.41  CNF conversion       : 0.02
% 2.87/1.41  Main loop            : 0.33
% 2.87/1.41  Inferencing          : 0.12
% 2.87/1.41  Reduction            : 0.10
% 2.87/1.41  Demodulation         : 0.07
% 2.87/1.41  BG Simplification    : 0.02
% 2.87/1.41  Subsumption          : 0.05
% 2.87/1.41  Abstraction          : 0.02
% 2.87/1.41  MUC search           : 0.00
% 2.87/1.41  Cooper               : 0.00
% 2.87/1.41  Total                : 0.68
% 2.87/1.41  Index Insertion      : 0.00
% 2.87/1.41  Index Deletion       : 0.00
% 2.87/1.41  Index Matching       : 0.00
% 2.87/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------

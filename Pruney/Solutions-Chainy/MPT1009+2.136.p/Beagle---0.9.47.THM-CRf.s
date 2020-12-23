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
% DateTime   : Thu Dec  3 10:15:01 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 205 expanded)
%              Number of leaves         :   46 (  92 expanded)
%              Depth                    :   11
%              Number of atoms          :  116 ( 385 expanded)
%              Number of equality atoms :   43 (  80 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_54,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_120,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_82,axiom,(
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

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_108,axiom,(
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

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_30,plain,(
    ! [A_19,B_20] : v1_relat_1(k2_zfmisc_1(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_99,plain,(
    ! [B_54,A_55] :
      ( v1_relat_1(B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_55))
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_102,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_64,c_99])).

tff(c_105,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_102])).

tff(c_118,plain,(
    ! [C_58,A_59,B_60] :
      ( v4_relat_1(C_58,A_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_122,plain,(
    v4_relat_1('#skF_6',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_64,c_118])).

tff(c_140,plain,(
    ! [B_66,A_67] :
      ( k7_relat_1(B_66,A_67) = B_66
      | ~ v4_relat_1(B_66,A_67)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_143,plain,
    ( k7_relat_1('#skF_6',k1_tarski('#skF_3')) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_122,c_140])).

tff(c_146,plain,(
    k7_relat_1('#skF_6',k1_tarski('#skF_3')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_143])).

tff(c_34,plain,(
    ! [B_24,A_23] :
      ( k2_relat_1(k7_relat_1(B_24,A_23)) = k9_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_150,plain,
    ( k9_relat_1('#skF_6',k1_tarski('#skF_3')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_34])).

tff(c_154,plain,(
    k9_relat_1('#skF_6',k1_tarski('#skF_3')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_150])).

tff(c_106,plain,(
    ! [B_56,A_57] :
      ( k2_relat_1(k7_relat_1(B_56,A_57)) = k9_relat_1(B_56,A_57)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_32,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k9_relat_1(B_22,A_21),k2_relat_1(B_22))
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_248,plain,(
    ! [B_101,A_102,A_103] :
      ( r1_tarski(k9_relat_1(k7_relat_1(B_101,A_102),A_103),k9_relat_1(B_101,A_102))
      | ~ v1_relat_1(k7_relat_1(B_101,A_102))
      | ~ v1_relat_1(B_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_32])).

tff(c_254,plain,(
    ! [A_103] :
      ( r1_tarski(k9_relat_1('#skF_6',A_103),k9_relat_1('#skF_6',k1_tarski('#skF_3')))
      | ~ v1_relat_1(k7_relat_1('#skF_6',k1_tarski('#skF_3')))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_248])).

tff(c_265,plain,(
    ! [A_103] : r1_tarski(k9_relat_1('#skF_6',A_103),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_105,c_146,c_154,c_254])).

tff(c_68,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_28,plain,(
    ! [A_16,B_18] :
      ( k9_relat_1(A_16,k1_tarski(B_18)) = k11_relat_1(A_16,B_18)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_159,plain,
    ( k11_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_28])).

tff(c_169,plain,(
    k11_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_159])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_66,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_218,plain,(
    ! [A_78,B_79,C_80] :
      ( k1_relset_1(A_78,B_79,C_80) = k1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_222,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_218])).

tff(c_289,plain,(
    ! [B_112,A_113,C_114] :
      ( k1_xboole_0 = B_112
      | k1_relset_1(A_113,B_112,C_114) = A_113
      | ~ v1_funct_2(C_114,A_113,B_112)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_113,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_292,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_6',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_289])).

tff(c_295,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_222,c_292])).

tff(c_296,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_295])).

tff(c_72,plain,(
    ! [A_48] : k2_tarski(A_48,A_48) = k1_tarski(A_48) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [D_6,A_1] : r2_hidden(D_6,k2_tarski(A_1,D_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_78,plain,(
    ! [A_48] : r2_hidden(A_48,k1_tarski(A_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_4])).

tff(c_313,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_78])).

tff(c_38,plain,(
    ! [B_28,A_27] :
      ( k1_tarski(k1_funct_1(B_28,A_27)) = k11_relat_1(B_28,A_27)
      | ~ r2_hidden(A_27,k1_relat_1(B_28))
      | ~ v1_funct_1(B_28)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_325,plain,
    ( k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k11_relat_1('#skF_6','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_313,c_38])).

tff(c_328,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_68,c_169,c_325])).

tff(c_228,plain,(
    ! [A_82,B_83,C_84,D_85] :
      ( k7_relset_1(A_82,B_83,C_84,D_85) = k9_relat_1(C_84,D_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_231,plain,(
    ! [D_85] : k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6',D_85) = k9_relat_1('#skF_6',D_85) ),
    inference(resolution,[status(thm)],[c_64,c_228])).

tff(c_60,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_233,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_60])).

tff(c_918,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_233])).

tff(c_921,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_918])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:19:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.48  
% 3.05/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.48  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.05/1.48  
% 3.05/1.48  %Foreground sorts:
% 3.05/1.48  
% 3.05/1.48  
% 3.05/1.48  %Background operators:
% 3.05/1.48  
% 3.05/1.48  
% 3.05/1.48  %Foreground operators:
% 3.05/1.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.05/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.05/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.05/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.05/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.05/1.48  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.05/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.05/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.05/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.05/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.05/1.48  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.05/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.05/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.05/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.05/1.48  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.05/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.05/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.05/1.48  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.05/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.05/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.05/1.48  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.05/1.48  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.05/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.05/1.48  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.05/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.05/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.05/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.05/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.05/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.05/1.48  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.05/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.05/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.05/1.48  
% 3.16/1.50  tff(f_54, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.16/1.50  tff(f_120, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 3.16/1.50  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.16/1.50  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.16/1.50  tff(f_68, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.16/1.50  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.16/1.50  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 3.16/1.50  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 3.16/1.50  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.16/1.50  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.16/1.50  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.16/1.50  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.16/1.50  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 3.16/1.50  tff(f_90, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.16/1.50  tff(c_30, plain, (![A_19, B_20]: (v1_relat_1(k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.16/1.50  tff(c_64, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.16/1.50  tff(c_99, plain, (![B_54, A_55]: (v1_relat_1(B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_55)) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.16/1.50  tff(c_102, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_64, c_99])).
% 3.16/1.50  tff(c_105, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_102])).
% 3.16/1.50  tff(c_118, plain, (![C_58, A_59, B_60]: (v4_relat_1(C_58, A_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.16/1.50  tff(c_122, plain, (v4_relat_1('#skF_6', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_64, c_118])).
% 3.16/1.50  tff(c_140, plain, (![B_66, A_67]: (k7_relat_1(B_66, A_67)=B_66 | ~v4_relat_1(B_66, A_67) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.16/1.50  tff(c_143, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_3'))='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_122, c_140])).
% 3.16/1.50  tff(c_146, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_3'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_105, c_143])).
% 3.16/1.50  tff(c_34, plain, (![B_24, A_23]: (k2_relat_1(k7_relat_1(B_24, A_23))=k9_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.16/1.50  tff(c_150, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_3'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_146, c_34])).
% 3.16/1.50  tff(c_154, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_3'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_150])).
% 3.16/1.50  tff(c_106, plain, (![B_56, A_57]: (k2_relat_1(k7_relat_1(B_56, A_57))=k9_relat_1(B_56, A_57) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.16/1.50  tff(c_32, plain, (![B_22, A_21]: (r1_tarski(k9_relat_1(B_22, A_21), k2_relat_1(B_22)) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.16/1.50  tff(c_248, plain, (![B_101, A_102, A_103]: (r1_tarski(k9_relat_1(k7_relat_1(B_101, A_102), A_103), k9_relat_1(B_101, A_102)) | ~v1_relat_1(k7_relat_1(B_101, A_102)) | ~v1_relat_1(B_101))), inference(superposition, [status(thm), theory('equality')], [c_106, c_32])).
% 3.16/1.50  tff(c_254, plain, (![A_103]: (r1_tarski(k9_relat_1('#skF_6', A_103), k9_relat_1('#skF_6', k1_tarski('#skF_3'))) | ~v1_relat_1(k7_relat_1('#skF_6', k1_tarski('#skF_3'))) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_146, c_248])).
% 3.16/1.50  tff(c_265, plain, (![A_103]: (r1_tarski(k9_relat_1('#skF_6', A_103), k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_105, c_146, c_154, c_254])).
% 3.16/1.50  tff(c_68, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.16/1.50  tff(c_28, plain, (![A_16, B_18]: (k9_relat_1(A_16, k1_tarski(B_18))=k11_relat_1(A_16, B_18) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.16/1.50  tff(c_159, plain, (k11_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_154, c_28])).
% 3.16/1.50  tff(c_169, plain, (k11_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_159])).
% 3.16/1.50  tff(c_62, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.16/1.50  tff(c_66, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.16/1.50  tff(c_218, plain, (![A_78, B_79, C_80]: (k1_relset_1(A_78, B_79, C_80)=k1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.16/1.50  tff(c_222, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_64, c_218])).
% 3.16/1.50  tff(c_289, plain, (![B_112, A_113, C_114]: (k1_xboole_0=B_112 | k1_relset_1(A_113, B_112, C_114)=A_113 | ~v1_funct_2(C_114, A_113, B_112) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_113, B_112))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.16/1.50  tff(c_292, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_6', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_64, c_289])).
% 3.16/1.50  tff(c_295, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_222, c_292])).
% 3.16/1.50  tff(c_296, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_62, c_295])).
% 3.16/1.50  tff(c_72, plain, (![A_48]: (k2_tarski(A_48, A_48)=k1_tarski(A_48))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.16/1.50  tff(c_4, plain, (![D_6, A_1]: (r2_hidden(D_6, k2_tarski(A_1, D_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.16/1.50  tff(c_78, plain, (![A_48]: (r2_hidden(A_48, k1_tarski(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_72, c_4])).
% 3.16/1.50  tff(c_313, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_296, c_78])).
% 3.16/1.50  tff(c_38, plain, (![B_28, A_27]: (k1_tarski(k1_funct_1(B_28, A_27))=k11_relat_1(B_28, A_27) | ~r2_hidden(A_27, k1_relat_1(B_28)) | ~v1_funct_1(B_28) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.16/1.50  tff(c_325, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k11_relat_1('#skF_6', '#skF_3') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_313, c_38])).
% 3.16/1.50  tff(c_328, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_68, c_169, c_325])).
% 3.16/1.50  tff(c_228, plain, (![A_82, B_83, C_84, D_85]: (k7_relset_1(A_82, B_83, C_84, D_85)=k9_relat_1(C_84, D_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.16/1.50  tff(c_231, plain, (![D_85]: (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', D_85)=k9_relat_1('#skF_6', D_85))), inference(resolution, [status(thm)], [c_64, c_228])).
% 3.16/1.50  tff(c_60, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.16/1.50  tff(c_233, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_60])).
% 3.16/1.50  tff(c_918, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_328, c_233])).
% 3.16/1.50  tff(c_921, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_265, c_918])).
% 3.16/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.50  
% 3.16/1.50  Inference rules
% 3.16/1.50  ----------------------
% 3.16/1.50  #Ref     : 0
% 3.16/1.50  #Sup     : 113
% 3.16/1.50  #Fact    : 2
% 3.16/1.50  #Define  : 0
% 3.16/1.50  #Split   : 0
% 3.16/1.50  #Chain   : 0
% 3.16/1.50  #Close   : 0
% 3.16/1.50  
% 3.16/1.50  Ordering : KBO
% 3.16/1.50  
% 3.16/1.50  Simplification rules
% 3.16/1.50  ----------------------
% 3.16/1.50  #Subsume      : 4
% 3.16/1.50  #Demod        : 63
% 3.16/1.50  #Tautology    : 49
% 3.16/1.50  #SimpNegUnit  : 4
% 3.16/1.50  #BackRed      : 9
% 3.16/1.50  
% 3.16/1.50  #Partial instantiations: 1008
% 3.16/1.50  #Strategies tried      : 1
% 3.16/1.50  
% 3.16/1.50  Timing (in seconds)
% 3.16/1.50  ----------------------
% 3.16/1.50  Preprocessing        : 0.37
% 3.16/1.50  Parsing              : 0.20
% 3.16/1.50  CNF conversion       : 0.02
% 3.16/1.50  Main loop            : 0.35
% 3.16/1.50  Inferencing          : 0.17
% 3.16/1.50  Reduction            : 0.09
% 3.16/1.50  Demodulation         : 0.07
% 3.16/1.50  BG Simplification    : 0.02
% 3.16/1.50  Subsumption          : 0.05
% 3.16/1.50  Abstraction          : 0.01
% 3.16/1.50  MUC search           : 0.00
% 3.16/1.50  Cooper               : 0.00
% 3.16/1.50  Total                : 0.75
% 3.16/1.50  Index Insertion      : 0.00
% 3.16/1.50  Index Deletion       : 0.00
% 3.16/1.50  Index Matching       : 0.00
% 3.16/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------

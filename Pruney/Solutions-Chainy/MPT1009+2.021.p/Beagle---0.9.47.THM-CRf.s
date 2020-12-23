%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:45 EST 2020

% Result     : Theorem 4.46s
% Output     : CNFRefutation 4.64s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 282 expanded)
%              Number of leaves         :   41 ( 115 expanded)
%              Depth                    :   13
%              Number of atoms          :  123 ( 582 expanded)
%              Number of equality atoms :   36 ( 138 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_118,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_106,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_74,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_167,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_184,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_167])).

tff(c_38,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k9_relat_1(B_22,A_21),k2_relat_1(B_22))
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_24,plain,(
    ! [B_12] : k2_zfmisc_1(k1_xboole_0,B_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1764,plain,(
    ! [B_223,A_224] :
      ( k1_tarski(k1_funct_1(B_223,A_224)) = k2_relat_1(B_223)
      | k1_tarski(A_224) != k1_relat_1(B_223)
      | ~ v1_funct_1(B_223)
      | ~ v1_relat_1(B_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1710,plain,(
    ! [A_211,B_212,C_213,D_214] :
      ( k7_relset_1(A_211,B_212,C_213,D_214) = k9_relat_1(C_213,D_214)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(A_211,B_212))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1727,plain,(
    ! [D_214] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_214) = k9_relat_1('#skF_4',D_214) ),
    inference(resolution,[status(thm)],[c_64,c_1710])).

tff(c_60,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1754,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1727,c_60])).

tff(c_1770,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1764,c_1754])).

tff(c_1779,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_68,c_1770])).

tff(c_1781,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1779])).

tff(c_442,plain,(
    ! [C_94,A_95,B_96] :
      ( v4_relat_1(C_94,A_95)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_461,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_442])).

tff(c_390,plain,(
    ! [B_90,A_91] :
      ( r1_tarski(k1_relat_1(B_90),A_91)
      | ~ v4_relat_1(B_90,A_91)
      | ~ v1_relat_1(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( k1_tarski(B_10) = A_9
      | k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k1_tarski(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2476,plain,(
    ! [B_288,B_289] :
      ( k1_tarski(B_288) = k1_relat_1(B_289)
      | k1_relat_1(B_289) = k1_xboole_0
      | ~ v4_relat_1(B_289,k1_tarski(B_288))
      | ~ v1_relat_1(B_289) ) ),
    inference(resolution,[status(thm)],[c_390,c_14])).

tff(c_2506,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_461,c_2476])).

tff(c_2525,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_2506])).

tff(c_2526,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1781,c_2525])).

tff(c_1649,plain,(
    ! [A_203] :
      ( m1_subset_1(A_203,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_203),k2_relat_1(A_203))))
      | ~ v1_funct_1(A_203)
      | ~ v1_relat_1(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1674,plain,(
    ! [A_203] :
      ( r1_tarski(A_203,k2_zfmisc_1(k1_relat_1(A_203),k2_relat_1(A_203)))
      | ~ v1_funct_1(A_203)
      | ~ v1_relat_1(A_203) ) ),
    inference(resolution,[status(thm)],[c_1649,c_28])).

tff(c_2561,plain,
    ( r1_tarski('#skF_4',k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_4')))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2526,c_1674])).

tff(c_2604,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_68,c_24,c_2561])).

tff(c_26,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_123,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_147,plain,(
    ! [A_50] : r1_tarski(k1_xboole_0,A_50) ),
    inference(resolution,[status(thm)],[c_26,c_123])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_150,plain,(
    ! [A_50] :
      ( k1_xboole_0 = A_50
      | ~ r1_tarski(A_50,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_147,c_2])).

tff(c_2642,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2604,c_150])).

tff(c_135,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(resolution,[status(thm)],[c_26,c_123])).

tff(c_2683,plain,(
    ! [A_13] : r1_tarski('#skF_4',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2642,c_135])).

tff(c_185,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_167])).

tff(c_40,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_198,plain,(
    ! [B_56,A_57] :
      ( r1_tarski(k9_relat_1(B_56,A_57),k2_relat_1(B_56))
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_203,plain,(
    ! [A_57] :
      ( r1_tarski(k9_relat_1(k1_xboole_0,A_57),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_198])).

tff(c_207,plain,(
    ! [A_58] : r1_tarski(k9_relat_1(k1_xboole_0,A_58),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_203])).

tff(c_212,plain,(
    ! [A_58] :
      ( k9_relat_1(k1_xboole_0,A_58) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k9_relat_1(k1_xboole_0,A_58)) ) ),
    inference(resolution,[status(thm)],[c_207,c_2])).

tff(c_216,plain,(
    ! [A_58] : k9_relat_1(k1_xboole_0,A_58) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_212])).

tff(c_2679,plain,(
    ! [A_58] : k9_relat_1('#skF_4',A_58) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2642,c_2642,c_216])).

tff(c_2870,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2679,c_1754])).

tff(c_2874,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2683,c_2870])).

tff(c_2875,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1779])).

tff(c_2943,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_2875])).

tff(c_2947,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_2943])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:02:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.46/1.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.46/1.80  
% 4.46/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.46/1.80  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.46/1.80  
% 4.46/1.80  %Foreground sorts:
% 4.46/1.80  
% 4.46/1.80  
% 4.46/1.80  %Background operators:
% 4.46/1.80  
% 4.46/1.80  
% 4.46/1.80  %Foreground operators:
% 4.46/1.80  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.46/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.46/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.46/1.80  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.46/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.46/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.46/1.80  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.46/1.80  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.46/1.80  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.46/1.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.46/1.80  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.46/1.80  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.46/1.80  tff('#skF_2', type, '#skF_2': $i).
% 4.46/1.80  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.46/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.46/1.80  tff('#skF_1', type, '#skF_1': $i).
% 4.46/1.80  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.46/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.46/1.80  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.46/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.46/1.80  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.46/1.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.46/1.80  tff('#skF_4', type, '#skF_4': $i).
% 4.46/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.46/1.80  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.46/1.80  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.46/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.46/1.80  
% 4.64/1.82  tff(f_118, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 4.64/1.82  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.64/1.82  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 4.64/1.82  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.64/1.82  tff(f_82, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 4.64/1.82  tff(f_96, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.64/1.82  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.64/1.82  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.64/1.82  tff(f_43, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.64/1.82  tff(f_106, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 4.64/1.82  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.64/1.82  tff(f_51, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.64/1.82  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.64/1.82  tff(f_74, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.64/1.82  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.64/1.82  tff(c_167, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.64/1.82  tff(c_184, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_167])).
% 4.64/1.82  tff(c_38, plain, (![B_22, A_21]: (r1_tarski(k9_relat_1(B_22, A_21), k2_relat_1(B_22)) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.64/1.82  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.64/1.82  tff(c_24, plain, (![B_12]: (k2_zfmisc_1(k1_xboole_0, B_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.64/1.82  tff(c_1764, plain, (![B_223, A_224]: (k1_tarski(k1_funct_1(B_223, A_224))=k2_relat_1(B_223) | k1_tarski(A_224)!=k1_relat_1(B_223) | ~v1_funct_1(B_223) | ~v1_relat_1(B_223))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.64/1.82  tff(c_1710, plain, (![A_211, B_212, C_213, D_214]: (k7_relset_1(A_211, B_212, C_213, D_214)=k9_relat_1(C_213, D_214) | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(A_211, B_212))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.64/1.82  tff(c_1727, plain, (![D_214]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_214)=k9_relat_1('#skF_4', D_214))), inference(resolution, [status(thm)], [c_64, c_1710])).
% 4.64/1.82  tff(c_60, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.64/1.82  tff(c_1754, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1727, c_60])).
% 4.64/1.82  tff(c_1770, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1764, c_1754])).
% 4.64/1.82  tff(c_1779, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_184, c_68, c_1770])).
% 4.64/1.82  tff(c_1781, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1779])).
% 4.64/1.82  tff(c_442, plain, (![C_94, A_95, B_96]: (v4_relat_1(C_94, A_95) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.64/1.82  tff(c_461, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_64, c_442])).
% 4.64/1.82  tff(c_390, plain, (![B_90, A_91]: (r1_tarski(k1_relat_1(B_90), A_91) | ~v4_relat_1(B_90, A_91) | ~v1_relat_1(B_90))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.64/1.82  tff(c_14, plain, (![B_10, A_9]: (k1_tarski(B_10)=A_9 | k1_xboole_0=A_9 | ~r1_tarski(A_9, k1_tarski(B_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.64/1.82  tff(c_2476, plain, (![B_288, B_289]: (k1_tarski(B_288)=k1_relat_1(B_289) | k1_relat_1(B_289)=k1_xboole_0 | ~v4_relat_1(B_289, k1_tarski(B_288)) | ~v1_relat_1(B_289))), inference(resolution, [status(thm)], [c_390, c_14])).
% 4.64/1.82  tff(c_2506, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_461, c_2476])).
% 4.64/1.82  tff(c_2525, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_184, c_2506])).
% 4.64/1.82  tff(c_2526, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1781, c_2525])).
% 4.64/1.82  tff(c_1649, plain, (![A_203]: (m1_subset_1(A_203, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_203), k2_relat_1(A_203)))) | ~v1_funct_1(A_203) | ~v1_relat_1(A_203))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.64/1.82  tff(c_28, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.64/1.82  tff(c_1674, plain, (![A_203]: (r1_tarski(A_203, k2_zfmisc_1(k1_relat_1(A_203), k2_relat_1(A_203))) | ~v1_funct_1(A_203) | ~v1_relat_1(A_203))), inference(resolution, [status(thm)], [c_1649, c_28])).
% 4.64/1.82  tff(c_2561, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_4'))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2526, c_1674])).
% 4.64/1.82  tff(c_2604, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_184, c_68, c_24, c_2561])).
% 4.64/1.82  tff(c_26, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.64/1.82  tff(c_123, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~m1_subset_1(A_46, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.64/1.82  tff(c_147, plain, (![A_50]: (r1_tarski(k1_xboole_0, A_50))), inference(resolution, [status(thm)], [c_26, c_123])).
% 4.64/1.82  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.64/1.82  tff(c_150, plain, (![A_50]: (k1_xboole_0=A_50 | ~r1_tarski(A_50, k1_xboole_0))), inference(resolution, [status(thm)], [c_147, c_2])).
% 4.64/1.82  tff(c_2642, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2604, c_150])).
% 4.64/1.82  tff(c_135, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(resolution, [status(thm)], [c_26, c_123])).
% 4.64/1.82  tff(c_2683, plain, (![A_13]: (r1_tarski('#skF_4', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_2642, c_135])).
% 4.64/1.82  tff(c_185, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_167])).
% 4.64/1.82  tff(c_40, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.64/1.82  tff(c_198, plain, (![B_56, A_57]: (r1_tarski(k9_relat_1(B_56, A_57), k2_relat_1(B_56)) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.64/1.82  tff(c_203, plain, (![A_57]: (r1_tarski(k9_relat_1(k1_xboole_0, A_57), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_198])).
% 4.64/1.82  tff(c_207, plain, (![A_58]: (r1_tarski(k9_relat_1(k1_xboole_0, A_58), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_203])).
% 4.64/1.82  tff(c_212, plain, (![A_58]: (k9_relat_1(k1_xboole_0, A_58)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k9_relat_1(k1_xboole_0, A_58)))), inference(resolution, [status(thm)], [c_207, c_2])).
% 4.64/1.82  tff(c_216, plain, (![A_58]: (k9_relat_1(k1_xboole_0, A_58)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_135, c_212])).
% 4.64/1.82  tff(c_2679, plain, (![A_58]: (k9_relat_1('#skF_4', A_58)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2642, c_2642, c_216])).
% 4.64/1.82  tff(c_2870, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2679, c_1754])).
% 4.64/1.82  tff(c_2874, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2683, c_2870])).
% 4.64/1.82  tff(c_2875, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_1779])).
% 4.64/1.82  tff(c_2943, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_2875])).
% 4.64/1.82  tff(c_2947, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_184, c_2943])).
% 4.64/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.64/1.82  
% 4.64/1.82  Inference rules
% 4.64/1.82  ----------------------
% 4.64/1.82  #Ref     : 0
% 4.64/1.82  #Sup     : 596
% 4.64/1.82  #Fact    : 0
% 4.64/1.82  #Define  : 0
% 4.64/1.82  #Split   : 4
% 4.64/1.82  #Chain   : 0
% 4.64/1.82  #Close   : 0
% 4.64/1.82  
% 4.64/1.82  Ordering : KBO
% 4.64/1.82  
% 4.64/1.82  Simplification rules
% 4.64/1.82  ----------------------
% 4.64/1.82  #Subsume      : 72
% 4.64/1.82  #Demod        : 918
% 4.64/1.82  #Tautology    : 339
% 4.64/1.82  #SimpNegUnit  : 2
% 4.64/1.82  #BackRed      : 108
% 4.64/1.82  
% 4.64/1.82  #Partial instantiations: 0
% 4.64/1.82  #Strategies tried      : 1
% 4.64/1.82  
% 4.64/1.82  Timing (in seconds)
% 4.64/1.82  ----------------------
% 4.64/1.82  Preprocessing        : 0.32
% 4.64/1.82  Parsing              : 0.17
% 4.64/1.82  CNF conversion       : 0.02
% 4.64/1.82  Main loop            : 0.70
% 4.64/1.82  Inferencing          : 0.22
% 4.64/1.82  Reduction            : 0.26
% 4.64/1.82  Demodulation         : 0.19
% 4.64/1.82  BG Simplification    : 0.03
% 4.64/1.82  Subsumption          : 0.14
% 4.64/1.82  Abstraction          : 0.03
% 4.64/1.82  MUC search           : 0.00
% 4.64/1.82  Cooper               : 0.00
% 4.64/1.82  Total                : 1.05
% 4.64/1.82  Index Insertion      : 0.00
% 4.64/1.82  Index Deletion       : 0.00
% 4.64/1.82  Index Matching       : 0.00
% 4.64/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------

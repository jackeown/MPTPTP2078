%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:02 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 139 expanded)
%              Number of leaves         :   40 (  67 expanded)
%              Depth                    :   10
%              Number of atoms          :  120 ( 272 expanded)
%              Number of equality atoms :   31 (  57 expanded)
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

tff(f_58,axiom,(
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

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_74,axiom,(
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

tff(c_28,plain,(
    ! [A_36,B_37] : v1_relat_1(k2_zfmisc_1(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_92,plain,(
    ! [B_67,A_68] :
      ( v1_relat_1(B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_68))
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_98,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_92])).

tff(c_102,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_98])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_957,plain,(
    ! [C_253,A_254,B_255] :
      ( m1_subset_1(C_253,k1_zfmisc_1(k2_zfmisc_1(A_254,B_255)))
      | ~ r1_tarski(k2_relat_1(C_253),B_255)
      | ~ r1_tarski(k1_relat_1(C_253),A_254)
      | ~ v1_relat_1(C_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_22,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | ~ m1_subset_1(A_31,k1_zfmisc_1(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1024,plain,(
    ! [C_264,A_265,B_266] :
      ( r1_tarski(C_264,k2_zfmisc_1(A_265,B_266))
      | ~ r1_tarski(k2_relat_1(C_264),B_266)
      | ~ r1_tarski(k1_relat_1(C_264),A_265)
      | ~ v1_relat_1(C_264) ) ),
    inference(resolution,[status(thm)],[c_957,c_22])).

tff(c_1028,plain,(
    ! [C_264,A_265] :
      ( r1_tarski(C_264,k2_zfmisc_1(A_265,k2_relat_1(C_264)))
      | ~ r1_tarski(k1_relat_1(C_264),A_265)
      | ~ v1_relat_1(C_264) ) ),
    inference(resolution,[status(thm)],[c_6,c_1024])).

tff(c_1029,plain,(
    ! [C_267,A_268] :
      ( r1_tarski(C_267,k2_zfmisc_1(A_268,k2_relat_1(C_267)))
      | ~ r1_tarski(k1_relat_1(C_267),A_268)
      | ~ v1_relat_1(C_267) ) ),
    inference(resolution,[status(thm)],[c_6,c_1024])).

tff(c_24,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1(A_31,k1_zfmisc_1(B_32))
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_192,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( k7_relset_1(A_95,B_96,C_97,D_98) = k9_relat_1(C_97,D_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_198,plain,(
    ! [A_95,B_96,A_31,D_98] :
      ( k7_relset_1(A_95,B_96,A_31,D_98) = k9_relat_1(A_31,D_98)
      | ~ r1_tarski(A_31,k2_zfmisc_1(A_95,B_96)) ) ),
    inference(resolution,[status(thm)],[c_24,c_192])).

tff(c_1103,plain,(
    ! [A_275,C_276,D_277] :
      ( k7_relset_1(A_275,k2_relat_1(C_276),C_276,D_277) = k9_relat_1(C_276,D_277)
      | ~ r1_tarski(k1_relat_1(C_276),A_275)
      | ~ v1_relat_1(C_276) ) ),
    inference(resolution,[status(thm)],[c_1029,c_198])).

tff(c_1121,plain,(
    ! [C_285,D_286] :
      ( k7_relset_1(k1_relat_1(C_285),k2_relat_1(C_285),C_285,D_286) = k9_relat_1(C_285,D_286)
      | ~ v1_relat_1(C_285) ) ),
    inference(resolution,[status(thm)],[c_6,c_1103])).

tff(c_740,plain,(
    ! [A_207,B_208,C_209,D_210] :
      ( m1_subset_1(k7_relset_1(A_207,B_208,C_209,D_210),k1_zfmisc_1(B_208))
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_813,plain,(
    ! [A_217,B_218,C_219,D_220] :
      ( r1_tarski(k7_relset_1(A_217,B_218,C_219,D_220),B_218)
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(A_217,B_218))) ) ),
    inference(resolution,[status(thm)],[c_740,c_22])).

tff(c_825,plain,(
    ! [A_217,B_218,A_31,D_220] :
      ( r1_tarski(k7_relset_1(A_217,B_218,A_31,D_220),B_218)
      | ~ r1_tarski(A_31,k2_zfmisc_1(A_217,B_218)) ) ),
    inference(resolution,[status(thm)],[c_24,c_813])).

tff(c_1136,plain,(
    ! [C_287,D_288] :
      ( r1_tarski(k9_relat_1(C_287,D_288),k2_relat_1(C_287))
      | ~ r1_tarski(C_287,k2_zfmisc_1(k1_relat_1(C_287),k2_relat_1(C_287)))
      | ~ v1_relat_1(C_287) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1121,c_825])).

tff(c_1139,plain,(
    ! [C_264,D_288] :
      ( r1_tarski(k9_relat_1(C_264,D_288),k2_relat_1(C_264))
      | ~ r1_tarski(k1_relat_1(C_264),k1_relat_1(C_264))
      | ~ v1_relat_1(C_264) ) ),
    inference(resolution,[status(thm)],[c_1028,c_1136])).

tff(c_1143,plain,(
    ! [C_289,D_290] :
      ( r1_tarski(k9_relat_1(C_289,D_290),k2_relat_1(C_289))
      | ~ v1_relat_1(C_289) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1139])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_241,plain,(
    ! [B_112,A_113] :
      ( k1_tarski(k1_funct_1(B_112,A_113)) = k2_relat_1(B_112)
      | k1_tarski(A_113) != k1_relat_1(B_112)
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_199,plain,(
    ! [D_98] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_98) = k9_relat_1('#skF_4',D_98) ),
    inference(resolution,[status(thm)],[c_56,c_192])).

tff(c_52,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_200,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_52])).

tff(c_247,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_200])).

tff(c_253,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_60,c_247])).

tff(c_255,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_253])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_58,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_143,plain,(
    ! [A_80,B_81,C_82] :
      ( k1_relset_1(A_80,B_81,C_82) = k1_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_152,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_143])).

tff(c_666,plain,(
    ! [B_204,A_205,C_206] :
      ( k1_xboole_0 = B_204
      | k1_relset_1(A_205,B_204,C_206) = A_205
      | ~ v1_funct_2(C_206,A_205,B_204)
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(A_205,B_204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_680,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_666])).

tff(c_686,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_152,c_680])).

tff(c_688,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_255,c_54,c_686])).

tff(c_689,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_253])).

tff(c_1146,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1143,c_689])).

tff(c_1155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_1146])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:58:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.52  
% 3.29/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.52  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.29/1.52  
% 3.29/1.52  %Foreground sorts:
% 3.29/1.52  
% 3.29/1.52  
% 3.29/1.52  %Background operators:
% 3.29/1.52  
% 3.29/1.52  
% 3.29/1.52  %Foreground operators:
% 3.29/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.29/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.29/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.29/1.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.29/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.29/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.29/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.29/1.52  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.29/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.29/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.29/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.29/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.29/1.52  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.29/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.29/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.29/1.52  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.29/1.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.29/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.29/1.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.29/1.52  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.29/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.29/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.29/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.29/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.52  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.29/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.29/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.29/1.52  
% 3.53/1.54  tff(f_58, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.53/1.54  tff(f_116, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 3.53/1.54  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.53/1.54  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.53/1.54  tff(f_86, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 3.53/1.54  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.53/1.54  tff(f_78, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.53/1.54  tff(f_70, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 3.53/1.54  tff(f_66, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.53/1.54  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.53/1.54  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.53/1.54  tff(c_28, plain, (![A_36, B_37]: (v1_relat_1(k2_zfmisc_1(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.53/1.54  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.53/1.54  tff(c_92, plain, (![B_67, A_68]: (v1_relat_1(B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(A_68)) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.53/1.54  tff(c_98, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_92])).
% 3.53/1.54  tff(c_102, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_98])).
% 3.53/1.54  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.53/1.54  tff(c_957, plain, (![C_253, A_254, B_255]: (m1_subset_1(C_253, k1_zfmisc_1(k2_zfmisc_1(A_254, B_255))) | ~r1_tarski(k2_relat_1(C_253), B_255) | ~r1_tarski(k1_relat_1(C_253), A_254) | ~v1_relat_1(C_253))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.53/1.54  tff(c_22, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | ~m1_subset_1(A_31, k1_zfmisc_1(B_32)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.53/1.54  tff(c_1024, plain, (![C_264, A_265, B_266]: (r1_tarski(C_264, k2_zfmisc_1(A_265, B_266)) | ~r1_tarski(k2_relat_1(C_264), B_266) | ~r1_tarski(k1_relat_1(C_264), A_265) | ~v1_relat_1(C_264))), inference(resolution, [status(thm)], [c_957, c_22])).
% 3.53/1.54  tff(c_1028, plain, (![C_264, A_265]: (r1_tarski(C_264, k2_zfmisc_1(A_265, k2_relat_1(C_264))) | ~r1_tarski(k1_relat_1(C_264), A_265) | ~v1_relat_1(C_264))), inference(resolution, [status(thm)], [c_6, c_1024])).
% 3.53/1.54  tff(c_1029, plain, (![C_267, A_268]: (r1_tarski(C_267, k2_zfmisc_1(A_268, k2_relat_1(C_267))) | ~r1_tarski(k1_relat_1(C_267), A_268) | ~v1_relat_1(C_267))), inference(resolution, [status(thm)], [c_6, c_1024])).
% 3.53/1.54  tff(c_24, plain, (![A_31, B_32]: (m1_subset_1(A_31, k1_zfmisc_1(B_32)) | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.53/1.54  tff(c_192, plain, (![A_95, B_96, C_97, D_98]: (k7_relset_1(A_95, B_96, C_97, D_98)=k9_relat_1(C_97, D_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.53/1.54  tff(c_198, plain, (![A_95, B_96, A_31, D_98]: (k7_relset_1(A_95, B_96, A_31, D_98)=k9_relat_1(A_31, D_98) | ~r1_tarski(A_31, k2_zfmisc_1(A_95, B_96)))), inference(resolution, [status(thm)], [c_24, c_192])).
% 3.53/1.54  tff(c_1103, plain, (![A_275, C_276, D_277]: (k7_relset_1(A_275, k2_relat_1(C_276), C_276, D_277)=k9_relat_1(C_276, D_277) | ~r1_tarski(k1_relat_1(C_276), A_275) | ~v1_relat_1(C_276))), inference(resolution, [status(thm)], [c_1029, c_198])).
% 3.53/1.54  tff(c_1121, plain, (![C_285, D_286]: (k7_relset_1(k1_relat_1(C_285), k2_relat_1(C_285), C_285, D_286)=k9_relat_1(C_285, D_286) | ~v1_relat_1(C_285))), inference(resolution, [status(thm)], [c_6, c_1103])).
% 3.53/1.54  tff(c_740, plain, (![A_207, B_208, C_209, D_210]: (m1_subset_1(k7_relset_1(A_207, B_208, C_209, D_210), k1_zfmisc_1(B_208)) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.53/1.54  tff(c_813, plain, (![A_217, B_218, C_219, D_220]: (r1_tarski(k7_relset_1(A_217, B_218, C_219, D_220), B_218) | ~m1_subset_1(C_219, k1_zfmisc_1(k2_zfmisc_1(A_217, B_218))))), inference(resolution, [status(thm)], [c_740, c_22])).
% 3.53/1.54  tff(c_825, plain, (![A_217, B_218, A_31, D_220]: (r1_tarski(k7_relset_1(A_217, B_218, A_31, D_220), B_218) | ~r1_tarski(A_31, k2_zfmisc_1(A_217, B_218)))), inference(resolution, [status(thm)], [c_24, c_813])).
% 3.53/1.54  tff(c_1136, plain, (![C_287, D_288]: (r1_tarski(k9_relat_1(C_287, D_288), k2_relat_1(C_287)) | ~r1_tarski(C_287, k2_zfmisc_1(k1_relat_1(C_287), k2_relat_1(C_287))) | ~v1_relat_1(C_287))), inference(superposition, [status(thm), theory('equality')], [c_1121, c_825])).
% 3.53/1.54  tff(c_1139, plain, (![C_264, D_288]: (r1_tarski(k9_relat_1(C_264, D_288), k2_relat_1(C_264)) | ~r1_tarski(k1_relat_1(C_264), k1_relat_1(C_264)) | ~v1_relat_1(C_264))), inference(resolution, [status(thm)], [c_1028, c_1136])).
% 3.53/1.54  tff(c_1143, plain, (![C_289, D_290]: (r1_tarski(k9_relat_1(C_289, D_290), k2_relat_1(C_289)) | ~v1_relat_1(C_289))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1139])).
% 3.53/1.54  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.53/1.54  tff(c_241, plain, (![B_112, A_113]: (k1_tarski(k1_funct_1(B_112, A_113))=k2_relat_1(B_112) | k1_tarski(A_113)!=k1_relat_1(B_112) | ~v1_funct_1(B_112) | ~v1_relat_1(B_112))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.53/1.54  tff(c_199, plain, (![D_98]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_98)=k9_relat_1('#skF_4', D_98))), inference(resolution, [status(thm)], [c_56, c_192])).
% 3.53/1.54  tff(c_52, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.53/1.54  tff(c_200, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_52])).
% 3.53/1.54  tff(c_247, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_241, c_200])).
% 3.53/1.54  tff(c_253, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_60, c_247])).
% 3.53/1.54  tff(c_255, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_253])).
% 3.53/1.54  tff(c_54, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.53/1.54  tff(c_58, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.53/1.54  tff(c_143, plain, (![A_80, B_81, C_82]: (k1_relset_1(A_80, B_81, C_82)=k1_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.53/1.54  tff(c_152, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_143])).
% 3.53/1.54  tff(c_666, plain, (![B_204, A_205, C_206]: (k1_xboole_0=B_204 | k1_relset_1(A_205, B_204, C_206)=A_205 | ~v1_funct_2(C_206, A_205, B_204) | ~m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1(A_205, B_204))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.53/1.54  tff(c_680, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_56, c_666])).
% 3.53/1.54  tff(c_686, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_152, c_680])).
% 3.53/1.54  tff(c_688, plain, $false, inference(negUnitSimplification, [status(thm)], [c_255, c_54, c_686])).
% 3.53/1.54  tff(c_689, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_253])).
% 3.53/1.54  tff(c_1146, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1143, c_689])).
% 3.53/1.54  tff(c_1155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_1146])).
% 3.53/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.54  
% 3.53/1.54  Inference rules
% 3.53/1.54  ----------------------
% 3.53/1.54  #Ref     : 0
% 3.53/1.54  #Sup     : 231
% 3.53/1.54  #Fact    : 0
% 3.53/1.54  #Define  : 0
% 3.53/1.54  #Split   : 5
% 3.53/1.54  #Chain   : 0
% 3.53/1.54  #Close   : 0
% 3.53/1.54  
% 3.53/1.54  Ordering : KBO
% 3.53/1.54  
% 3.53/1.54  Simplification rules
% 3.53/1.54  ----------------------
% 3.53/1.54  #Subsume      : 15
% 3.53/1.54  #Demod        : 60
% 3.53/1.54  #Tautology    : 69
% 3.53/1.54  #SimpNegUnit  : 3
% 3.53/1.54  #BackRed      : 7
% 3.53/1.54  
% 3.53/1.54  #Partial instantiations: 0
% 3.53/1.54  #Strategies tried      : 1
% 3.53/1.54  
% 3.53/1.54  Timing (in seconds)
% 3.53/1.54  ----------------------
% 3.53/1.54  Preprocessing        : 0.34
% 3.53/1.54  Parsing              : 0.17
% 3.53/1.54  CNF conversion       : 0.02
% 3.53/1.54  Main loop            : 0.43
% 3.53/1.54  Inferencing          : 0.16
% 3.53/1.54  Reduction            : 0.13
% 3.53/1.54  Demodulation         : 0.09
% 3.53/1.54  BG Simplification    : 0.03
% 3.53/1.54  Subsumption          : 0.08
% 3.53/1.54  Abstraction          : 0.03
% 3.53/1.54  MUC search           : 0.00
% 3.53/1.54  Cooper               : 0.00
% 3.53/1.54  Total                : 0.80
% 3.53/1.54  Index Insertion      : 0.00
% 3.53/1.54  Index Deletion       : 0.00
% 3.53/1.54  Index Matching       : 0.00
% 3.53/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------

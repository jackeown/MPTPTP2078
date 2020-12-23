%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:17 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 125 expanded)
%              Number of leaves         :   28 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :  131 ( 310 expanded)
%              Number of equality atoms :   50 ( 144 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & ~ ( B = k1_tarski(A)
            & C = k1_tarski(A) )
        & ~ ( B = k1_xboole_0
            & C = k1_tarski(A) )
        & ~ ( B = k1_tarski(A)
            & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ~ ( r1_tarski(C,A)
          & r1_tarski(C,B)
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_46,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_50,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    ! [A_34,B_35] :
      ( k2_xboole_0(A_34,B_35) = B_35
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_109,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_98])).

tff(c_42,plain,(
    ! [A_20] :
      ( k6_domain_1(A_20,'#skF_1'(A_20)) = A_20
      | ~ v1_zfmisc_1(A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_44,plain,(
    ! [A_20] :
      ( m1_subset_1('#skF_1'(A_20),A_20)
      | ~ v1_zfmisc_1(A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_205,plain,(
    ! [A_48,B_49] :
      ( k6_domain_1(A_48,B_49) = k1_tarski(B_49)
      | ~ m1_subset_1(B_49,A_48)
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_504,plain,(
    ! [A_103] :
      ( k6_domain_1(A_103,'#skF_1'(A_103)) = k1_tarski('#skF_1'(A_103))
      | ~ v1_zfmisc_1(A_103)
      | v1_xboole_0(A_103) ) ),
    inference(resolution,[status(thm)],[c_44,c_205])).

tff(c_548,plain,(
    ! [A_111] :
      ( k1_tarski('#skF_1'(A_111)) = A_111
      | ~ v1_zfmisc_1(A_111)
      | v1_xboole_0(A_111)
      | ~ v1_zfmisc_1(A_111)
      | v1_xboole_0(A_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_504])).

tff(c_30,plain,(
    ! [A_13,C_15,B_14] :
      ( k1_tarski(A_13) = C_15
      | k1_tarski(A_13) = B_14
      | k2_xboole_0(B_14,C_15) != k1_tarski(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1132,plain,(
    ! [A_184,C_185,B_186] :
      ( k1_tarski('#skF_1'(A_184)) = C_185
      | k1_tarski('#skF_1'(A_184)) = B_186
      | k2_xboole_0(B_186,C_185) != A_184
      | ~ v1_zfmisc_1(A_184)
      | v1_xboole_0(A_184)
      | ~ v1_zfmisc_1(A_184)
      | v1_xboole_0(A_184) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_548,c_30])).

tff(c_1141,plain,(
    ! [B_187] :
      ( k1_tarski('#skF_1'(B_187)) = B_187
      | ~ v1_zfmisc_1(B_187)
      | v1_xboole_0(B_187) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_1132])).

tff(c_48,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_110,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_48,c_98])).

tff(c_210,plain,(
    ! [B_50,A_51,C_52] :
      ( k1_xboole_0 = B_50
      | k1_tarski(A_51) = B_50
      | k2_xboole_0(B_50,C_52) != k1_tarski(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_216,plain,(
    ! [A_51] :
      ( k1_xboole_0 = '#skF_2'
      | k1_tarski(A_51) = '#skF_2'
      | k1_tarski(A_51) != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_210])).

tff(c_221,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_216])).

tff(c_14,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_231,plain,(
    ! [A_7] : k4_xboole_0('#skF_2',A_7) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_221,c_14])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_230,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_8])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( r1_xboole_0(k1_tarski(A_11),B_12)
      | r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_346,plain,(
    ! [A_67,B_68,C_69] :
      ( ~ r1_xboole_0(A_67,B_68)
      | ~ r1_tarski(C_69,B_68)
      | ~ r1_tarski(C_69,A_67)
      | v1_xboole_0(C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_409,plain,(
    ! [C_82,B_83,A_84] :
      ( ~ r1_tarski(C_82,B_83)
      | ~ r1_tarski(C_82,k1_tarski(A_84))
      | v1_xboole_0(C_82)
      | r2_hidden(A_84,B_83) ) ),
    inference(resolution,[status(thm)],[c_18,c_346])).

tff(c_415,plain,(
    ! [A_84] :
      ( ~ r1_tarski('#skF_2',k1_tarski(A_84))
      | v1_xboole_0('#skF_2')
      | r2_hidden(A_84,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_409])).

tff(c_421,plain,(
    ! [A_85] :
      ( ~ r1_tarski('#skF_2',k1_tarski(A_85))
      | r2_hidden(A_85,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_415])).

tff(c_424,plain,(
    ! [A_85] :
      ( r2_hidden(A_85,'#skF_3')
      | k4_xboole_0('#skF_2',k1_tarski(A_85)) != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_230,c_421])).

tff(c_429,plain,(
    ! [A_86] : r2_hidden(A_86,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_424])).

tff(c_36,plain,(
    ! [B_17,A_16] :
      ( ~ r1_tarski(B_17,A_16)
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_434,plain,(
    ! [A_87] : ~ r1_tarski('#skF_3',A_87) ),
    inference(resolution,[status(thm)],[c_429,c_36])).

tff(c_444,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_434])).

tff(c_445,plain,(
    ! [A_51] :
      ( k1_tarski(A_51) = '#skF_2'
      | k1_tarski(A_51) != '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_1242,plain,(
    ! [B_191] :
      ( k1_tarski('#skF_1'(B_191)) = '#skF_2'
      | B_191 != '#skF_3'
      | ~ v1_zfmisc_1(B_191)
      | v1_xboole_0(B_191) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1141,c_445])).

tff(c_1140,plain,(
    ! [B_2] :
      ( k1_tarski('#skF_1'(B_2)) = B_2
      | ~ v1_zfmisc_1(B_2)
      | v1_xboole_0(B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_1132])).

tff(c_1434,plain,(
    ! [B_213] :
      ( B_213 = '#skF_2'
      | ~ v1_zfmisc_1(B_213)
      | v1_xboole_0(B_213)
      | B_213 != '#skF_3'
      | ~ v1_zfmisc_1(B_213)
      | v1_xboole_0(B_213) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1242,c_1140])).

tff(c_1436,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1434])).

tff(c_1439,plain,
    ( '#skF_2' = '#skF_3'
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1436])).

tff(c_1441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_1439])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:52:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.56/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.67  
% 3.56/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.67  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 3.56/1.67  
% 3.56/1.67  %Foreground sorts:
% 3.56/1.67  
% 3.56/1.67  
% 3.56/1.67  %Background operators:
% 3.56/1.67  
% 3.56/1.67  
% 3.56/1.67  %Foreground operators:
% 3.56/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.56/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.56/1.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.56/1.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.56/1.67  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.56/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.56/1.67  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.56/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.56/1.67  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.56/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.56/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.56/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.56/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.56/1.67  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.56/1.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.56/1.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.56/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.56/1.67  
% 3.56/1.68  tff(f_110, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 3.56/1.68  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.56/1.68  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.56/1.68  tff(f_96, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 3.56/1.68  tff(f_86, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.56/1.68  tff(f_74, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.56/1.68  tff(f_41, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 3.56/1.68  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.56/1.68  tff(f_56, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.56/1.68  tff(f_51, axiom, (![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_xboole_1)).
% 3.56/1.68  tff(f_79, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.56/1.68  tff(c_52, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.56/1.68  tff(c_46, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.56/1.68  tff(c_50, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.56/1.68  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.56/1.68  tff(c_98, plain, (![A_34, B_35]: (k2_xboole_0(A_34, B_35)=B_35 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.56/1.68  tff(c_109, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_98])).
% 3.56/1.68  tff(c_42, plain, (![A_20]: (k6_domain_1(A_20, '#skF_1'(A_20))=A_20 | ~v1_zfmisc_1(A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.56/1.68  tff(c_44, plain, (![A_20]: (m1_subset_1('#skF_1'(A_20), A_20) | ~v1_zfmisc_1(A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.56/1.68  tff(c_205, plain, (![A_48, B_49]: (k6_domain_1(A_48, B_49)=k1_tarski(B_49) | ~m1_subset_1(B_49, A_48) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.56/1.68  tff(c_504, plain, (![A_103]: (k6_domain_1(A_103, '#skF_1'(A_103))=k1_tarski('#skF_1'(A_103)) | ~v1_zfmisc_1(A_103) | v1_xboole_0(A_103))), inference(resolution, [status(thm)], [c_44, c_205])).
% 3.56/1.68  tff(c_548, plain, (![A_111]: (k1_tarski('#skF_1'(A_111))=A_111 | ~v1_zfmisc_1(A_111) | v1_xboole_0(A_111) | ~v1_zfmisc_1(A_111) | v1_xboole_0(A_111))), inference(superposition, [status(thm), theory('equality')], [c_42, c_504])).
% 3.56/1.68  tff(c_30, plain, (![A_13, C_15, B_14]: (k1_tarski(A_13)=C_15 | k1_tarski(A_13)=B_14 | k2_xboole_0(B_14, C_15)!=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.56/1.68  tff(c_1132, plain, (![A_184, C_185, B_186]: (k1_tarski('#skF_1'(A_184))=C_185 | k1_tarski('#skF_1'(A_184))=B_186 | k2_xboole_0(B_186, C_185)!=A_184 | ~v1_zfmisc_1(A_184) | v1_xboole_0(A_184) | ~v1_zfmisc_1(A_184) | v1_xboole_0(A_184))), inference(superposition, [status(thm), theory('equality')], [c_548, c_30])).
% 3.56/1.68  tff(c_1141, plain, (![B_187]: (k1_tarski('#skF_1'(B_187))=B_187 | ~v1_zfmisc_1(B_187) | v1_xboole_0(B_187))), inference(superposition, [status(thm), theory('equality')], [c_109, c_1132])).
% 3.56/1.68  tff(c_48, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.56/1.68  tff(c_110, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_48, c_98])).
% 3.56/1.68  tff(c_210, plain, (![B_50, A_51, C_52]: (k1_xboole_0=B_50 | k1_tarski(A_51)=B_50 | k2_xboole_0(B_50, C_52)!=k1_tarski(A_51))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.56/1.68  tff(c_216, plain, (![A_51]: (k1_xboole_0='#skF_2' | k1_tarski(A_51)='#skF_2' | k1_tarski(A_51)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_110, c_210])).
% 3.56/1.68  tff(c_221, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_216])).
% 3.56/1.68  tff(c_14, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.56/1.68  tff(c_231, plain, (![A_7]: (k4_xboole_0('#skF_2', A_7)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_221, c_221, c_14])).
% 3.56/1.68  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.56/1.68  tff(c_230, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_221, c_8])).
% 3.56/1.68  tff(c_54, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.56/1.68  tff(c_18, plain, (![A_11, B_12]: (r1_xboole_0(k1_tarski(A_11), B_12) | r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.56/1.68  tff(c_346, plain, (![A_67, B_68, C_69]: (~r1_xboole_0(A_67, B_68) | ~r1_tarski(C_69, B_68) | ~r1_tarski(C_69, A_67) | v1_xboole_0(C_69))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.56/1.68  tff(c_409, plain, (![C_82, B_83, A_84]: (~r1_tarski(C_82, B_83) | ~r1_tarski(C_82, k1_tarski(A_84)) | v1_xboole_0(C_82) | r2_hidden(A_84, B_83))), inference(resolution, [status(thm)], [c_18, c_346])).
% 3.56/1.68  tff(c_415, plain, (![A_84]: (~r1_tarski('#skF_2', k1_tarski(A_84)) | v1_xboole_0('#skF_2') | r2_hidden(A_84, '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_409])).
% 3.56/1.68  tff(c_421, plain, (![A_85]: (~r1_tarski('#skF_2', k1_tarski(A_85)) | r2_hidden(A_85, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_54, c_415])).
% 3.56/1.68  tff(c_424, plain, (![A_85]: (r2_hidden(A_85, '#skF_3') | k4_xboole_0('#skF_2', k1_tarski(A_85))!='#skF_2')), inference(resolution, [status(thm)], [c_230, c_421])).
% 3.56/1.68  tff(c_429, plain, (![A_86]: (r2_hidden(A_86, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_424])).
% 3.56/1.68  tff(c_36, plain, (![B_17, A_16]: (~r1_tarski(B_17, A_16) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.56/1.68  tff(c_434, plain, (![A_87]: (~r1_tarski('#skF_3', A_87))), inference(resolution, [status(thm)], [c_429, c_36])).
% 3.56/1.68  tff(c_444, plain, $false, inference(resolution, [status(thm)], [c_6, c_434])).
% 3.56/1.68  tff(c_445, plain, (![A_51]: (k1_tarski(A_51)='#skF_2' | k1_tarski(A_51)!='#skF_3')), inference(splitRight, [status(thm)], [c_216])).
% 3.56/1.68  tff(c_1242, plain, (![B_191]: (k1_tarski('#skF_1'(B_191))='#skF_2' | B_191!='#skF_3' | ~v1_zfmisc_1(B_191) | v1_xboole_0(B_191))), inference(superposition, [status(thm), theory('equality')], [c_1141, c_445])).
% 3.56/1.68  tff(c_1140, plain, (![B_2]: (k1_tarski('#skF_1'(B_2))=B_2 | ~v1_zfmisc_1(B_2) | v1_xboole_0(B_2))), inference(superposition, [status(thm), theory('equality')], [c_109, c_1132])).
% 3.56/1.68  tff(c_1434, plain, (![B_213]: (B_213='#skF_2' | ~v1_zfmisc_1(B_213) | v1_xboole_0(B_213) | B_213!='#skF_3' | ~v1_zfmisc_1(B_213) | v1_xboole_0(B_213))), inference(superposition, [status(thm), theory('equality')], [c_1242, c_1140])).
% 3.56/1.68  tff(c_1436, plain, ('#skF_2'='#skF_3' | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_1434])).
% 3.56/1.68  tff(c_1439, plain, ('#skF_2'='#skF_3' | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1436])).
% 3.56/1.68  tff(c_1441, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_46, c_1439])).
% 3.56/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.68  
% 3.56/1.68  Inference rules
% 3.56/1.68  ----------------------
% 3.56/1.68  #Ref     : 3
% 3.56/1.68  #Sup     : 325
% 3.56/1.68  #Fact    : 0
% 3.56/1.68  #Define  : 0
% 3.56/1.68  #Split   : 3
% 3.56/1.68  #Chain   : 0
% 3.56/1.68  #Close   : 0
% 3.56/1.68  
% 3.56/1.68  Ordering : KBO
% 3.56/1.68  
% 3.56/1.68  Simplification rules
% 3.56/1.68  ----------------------
% 3.56/1.68  #Subsume      : 68
% 3.56/1.68  #Demod        : 46
% 3.56/1.68  #Tautology    : 94
% 3.56/1.68  #SimpNegUnit  : 20
% 3.56/1.68  #BackRed      : 10
% 3.56/1.68  
% 3.56/1.68  #Partial instantiations: 0
% 3.56/1.68  #Strategies tried      : 1
% 3.56/1.68  
% 3.56/1.68  Timing (in seconds)
% 3.56/1.68  ----------------------
% 3.56/1.69  Preprocessing        : 0.31
% 3.56/1.69  Parsing              : 0.16
% 3.56/1.69  CNF conversion       : 0.02
% 3.56/1.69  Main loop            : 0.54
% 3.56/1.69  Inferencing          : 0.20
% 3.56/1.69  Reduction            : 0.14
% 3.56/1.69  Demodulation         : 0.09
% 3.56/1.69  BG Simplification    : 0.03
% 3.56/1.69  Subsumption          : 0.14
% 3.56/1.69  Abstraction          : 0.02
% 3.56/1.69  MUC search           : 0.00
% 3.56/1.69  Cooper               : 0.00
% 3.56/1.69  Total                : 0.88
% 3.56/1.69  Index Insertion      : 0.00
% 3.56/1.69  Index Deletion       : 0.00
% 3.56/1.69  Index Matching       : 0.00
% 3.56/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------

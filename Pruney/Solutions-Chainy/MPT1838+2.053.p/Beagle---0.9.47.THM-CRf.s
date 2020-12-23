%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:21 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 172 expanded)
%              Number of leaves         :   26 (  69 expanded)
%              Depth                    :   13
%              Number of atoms          :  141 ( 487 expanded)
%              Number of equality atoms :   66 ( 217 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(f_29,axiom,(
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

tff(f_77,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & ~ ( B = k1_tarski(A)
            & C = k1_tarski(A) )
        & ~ ( B = k1_xboole_0
            & C = k1_tarski(A) )
        & ~ ( B = k1_tarski(A)
            & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_50,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_119,plain,(
    ! [A_37,B_38] :
      ( k2_xboole_0(A_37,B_38) = B_38
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_127,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_50,c_119])).

tff(c_46,plain,(
    ! [A_24] :
      ( m1_subset_1('#skF_1'(A_24),A_24)
      | ~ v1_zfmisc_1(A_24)
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_173,plain,(
    ! [A_47,B_48] :
      ( k6_domain_1(A_47,B_48) = k1_tarski(B_48)
      | ~ m1_subset_1(B_48,A_47)
      | v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_239,plain,(
    ! [A_65] :
      ( k6_domain_1(A_65,'#skF_1'(A_65)) = k1_tarski('#skF_1'(A_65))
      | ~ v1_zfmisc_1(A_65)
      | v1_xboole_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_46,c_173])).

tff(c_44,plain,(
    ! [A_24] :
      ( k6_domain_1(A_24,'#skF_1'(A_24)) = A_24
      | ~ v1_zfmisc_1(A_24)
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_321,plain,(
    ! [A_84] :
      ( k1_tarski('#skF_1'(A_84)) = A_84
      | ~ v1_zfmisc_1(A_84)
      | v1_xboole_0(A_84)
      | ~ v1_zfmisc_1(A_84)
      | v1_xboole_0(A_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_44])).

tff(c_22,plain,(
    ! [A_17,C_19,B_18] :
      ( k1_tarski(A_17) = C_19
      | k1_xboole_0 = C_19
      | k2_xboole_0(B_18,C_19) != k1_tarski(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_412,plain,(
    ! [A_89,C_90,B_91] :
      ( k1_tarski('#skF_1'(A_89)) = C_90
      | k1_xboole_0 = C_90
      | k2_xboole_0(B_91,C_90) != A_89
      | ~ v1_zfmisc_1(A_89)
      | v1_xboole_0(A_89)
      | ~ v1_zfmisc_1(A_89)
      | v1_xboole_0(A_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_22])).

tff(c_414,plain,(
    ! [A_89] :
      ( k1_tarski('#skF_1'(A_89)) = '#skF_3'
      | k1_xboole_0 = '#skF_3'
      | A_89 != '#skF_3'
      | ~ v1_zfmisc_1(A_89)
      | v1_xboole_0(A_89)
      | ~ v1_zfmisc_1(A_89)
      | v1_xboole_0(A_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_412])).

tff(c_523,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_414])).

tff(c_4,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_4] : r1_xboole_0(A_4,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_141,plain,(
    ! [B_40,A_41] :
      ( ~ r1_xboole_0(B_40,A_41)
      | ~ r1_tarski(B_40,A_41)
      | v1_xboole_0(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_146,plain,(
    ! [A_42] :
      ( ~ r1_tarski(A_42,k1_xboole_0)
      | v1_xboole_0(A_42) ) ),
    inference(resolution,[status(thm)],[c_6,c_141])).

tff(c_151,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_146])).

tff(c_535,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_151])).

tff(c_543,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_535])).

tff(c_545,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_414])).

tff(c_52,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_48,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_126,plain,(
    ! [A_3] : k2_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(resolution,[status(thm)],[c_4,c_119])).

tff(c_421,plain,(
    ! [A_92] :
      ( k1_tarski('#skF_1'(A_92)) = A_92
      | k1_xboole_0 = A_92
      | ~ v1_zfmisc_1(A_92)
      | v1_xboole_0(A_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_412])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_188,plain,(
    ! [B_52,A_53,C_54] :
      ( k1_xboole_0 = B_52
      | k1_tarski(A_53) = B_52
      | k2_xboole_0(B_52,C_54) != k1_tarski(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_191,plain,(
    ! [A_53] :
      ( k1_xboole_0 = '#skF_2'
      | k1_tarski(A_53) = '#skF_2'
      | k1_tarski(A_53) != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_188])).

tff(c_199,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_191])).

tff(c_208,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_151])).

tff(c_216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_208])).

tff(c_217,plain,(
    ! [A_53] :
      ( k1_tarski(A_53) = '#skF_2'
      | k1_tarski(A_53) != '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_448,plain,(
    ! [A_92] :
      ( k1_tarski('#skF_1'(A_92)) = '#skF_2'
      | A_92 != '#skF_3'
      | k1_xboole_0 = A_92
      | ~ v1_zfmisc_1(A_92)
      | v1_xboole_0(A_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_217])).

tff(c_644,plain,(
    ! [A_100,C_101,B_102] :
      ( k1_tarski('#skF_1'(A_100)) = C_101
      | k1_xboole_0 = C_101
      | k2_xboole_0(B_102,C_101) != A_100
      | k1_xboole_0 = A_100
      | ~ v1_zfmisc_1(A_100)
      | v1_xboole_0(A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_22])).

tff(c_646,plain,(
    ! [A_100] :
      ( k1_tarski('#skF_1'(A_100)) = '#skF_3'
      | k1_xboole_0 = '#skF_3'
      | A_100 != '#skF_3'
      | k1_xboole_0 = A_100
      | ~ v1_zfmisc_1(A_100)
      | v1_xboole_0(A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_644])).

tff(c_672,plain,(
    ! [A_105] :
      ( k1_tarski('#skF_1'(A_105)) = '#skF_3'
      | A_105 != '#skF_3'
      | k1_xboole_0 = A_105
      | ~ v1_zfmisc_1(A_105)
      | v1_xboole_0(A_105) ) ),
    inference(negUnitSimplification,[status(thm)],[c_545,c_646])).

tff(c_727,plain,(
    ! [A_92] :
      ( '#skF_2' = '#skF_3'
      | A_92 != '#skF_3'
      | k1_xboole_0 = A_92
      | ~ v1_zfmisc_1(A_92)
      | v1_xboole_0(A_92)
      | A_92 != '#skF_3'
      | k1_xboole_0 = A_92
      | ~ v1_zfmisc_1(A_92)
      | v1_xboole_0(A_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_448,c_672])).

tff(c_747,plain,(
    ! [A_106] :
      ( A_106 != '#skF_3'
      | k1_xboole_0 = A_106
      | ~ v1_zfmisc_1(A_106)
      | v1_xboole_0(A_106)
      | A_106 != '#skF_3'
      | k1_xboole_0 = A_106
      | ~ v1_zfmisc_1(A_106)
      | v1_xboole_0(A_106) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_727])).

tff(c_749,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_747])).

tff(c_752,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_749])).

tff(c_754,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_545,c_752])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:16:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.00/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.45  
% 3.00/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.45  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 3.00/1.45  
% 3.00/1.45  %Foreground sorts:
% 3.00/1.45  
% 3.00/1.45  
% 3.00/1.45  %Background operators:
% 3.00/1.45  
% 3.00/1.45  
% 3.00/1.45  %Foreground operators:
% 3.00/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.00/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.00/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.00/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.00/1.45  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.00/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.00/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.00/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.00/1.45  tff('#skF_2', type, '#skF_2': $i).
% 3.00/1.45  tff('#skF_3', type, '#skF_3': $i).
% 3.00/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.00/1.45  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.00/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.00/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.00/1.45  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.00/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.00/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.00/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.00/1.45  
% 3.18/1.46  tff(f_110, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 3.18/1.46  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.18/1.46  tff(f_96, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 3.18/1.46  tff(f_86, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.18/1.46  tff(f_77, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.18/1.46  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.18/1.46  tff(f_33, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.18/1.46  tff(f_41, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.18/1.46  tff(c_54, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.18/1.46  tff(c_50, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.18/1.46  tff(c_119, plain, (![A_37, B_38]: (k2_xboole_0(A_37, B_38)=B_38 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.18/1.46  tff(c_127, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_50, c_119])).
% 3.18/1.46  tff(c_46, plain, (![A_24]: (m1_subset_1('#skF_1'(A_24), A_24) | ~v1_zfmisc_1(A_24) | v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.18/1.46  tff(c_173, plain, (![A_47, B_48]: (k6_domain_1(A_47, B_48)=k1_tarski(B_48) | ~m1_subset_1(B_48, A_47) | v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.18/1.46  tff(c_239, plain, (![A_65]: (k6_domain_1(A_65, '#skF_1'(A_65))=k1_tarski('#skF_1'(A_65)) | ~v1_zfmisc_1(A_65) | v1_xboole_0(A_65))), inference(resolution, [status(thm)], [c_46, c_173])).
% 3.18/1.46  tff(c_44, plain, (![A_24]: (k6_domain_1(A_24, '#skF_1'(A_24))=A_24 | ~v1_zfmisc_1(A_24) | v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.18/1.46  tff(c_321, plain, (![A_84]: (k1_tarski('#skF_1'(A_84))=A_84 | ~v1_zfmisc_1(A_84) | v1_xboole_0(A_84) | ~v1_zfmisc_1(A_84) | v1_xboole_0(A_84))), inference(superposition, [status(thm), theory('equality')], [c_239, c_44])).
% 3.18/1.46  tff(c_22, plain, (![A_17, C_19, B_18]: (k1_tarski(A_17)=C_19 | k1_xboole_0=C_19 | k2_xboole_0(B_18, C_19)!=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.18/1.46  tff(c_412, plain, (![A_89, C_90, B_91]: (k1_tarski('#skF_1'(A_89))=C_90 | k1_xboole_0=C_90 | k2_xboole_0(B_91, C_90)!=A_89 | ~v1_zfmisc_1(A_89) | v1_xboole_0(A_89) | ~v1_zfmisc_1(A_89) | v1_xboole_0(A_89))), inference(superposition, [status(thm), theory('equality')], [c_321, c_22])).
% 3.18/1.46  tff(c_414, plain, (![A_89]: (k1_tarski('#skF_1'(A_89))='#skF_3' | k1_xboole_0='#skF_3' | A_89!='#skF_3' | ~v1_zfmisc_1(A_89) | v1_xboole_0(A_89) | ~v1_zfmisc_1(A_89) | v1_xboole_0(A_89))), inference(superposition, [status(thm), theory('equality')], [c_127, c_412])).
% 3.18/1.46  tff(c_523, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_414])).
% 3.18/1.46  tff(c_4, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.18/1.46  tff(c_6, plain, (![A_4]: (r1_xboole_0(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.18/1.46  tff(c_141, plain, (![B_40, A_41]: (~r1_xboole_0(B_40, A_41) | ~r1_tarski(B_40, A_41) | v1_xboole_0(B_40))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.18/1.46  tff(c_146, plain, (![A_42]: (~r1_tarski(A_42, k1_xboole_0) | v1_xboole_0(A_42))), inference(resolution, [status(thm)], [c_6, c_141])).
% 3.18/1.46  tff(c_151, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_146])).
% 3.18/1.46  tff(c_535, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_523, c_151])).
% 3.18/1.46  tff(c_543, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_535])).
% 3.18/1.46  tff(c_545, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_414])).
% 3.18/1.46  tff(c_52, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.18/1.46  tff(c_48, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.18/1.46  tff(c_126, plain, (![A_3]: (k2_xboole_0(k1_xboole_0, A_3)=A_3)), inference(resolution, [status(thm)], [c_4, c_119])).
% 3.18/1.46  tff(c_421, plain, (![A_92]: (k1_tarski('#skF_1'(A_92))=A_92 | k1_xboole_0=A_92 | ~v1_zfmisc_1(A_92) | v1_xboole_0(A_92))), inference(superposition, [status(thm), theory('equality')], [c_126, c_412])).
% 3.18/1.46  tff(c_56, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.18/1.46  tff(c_188, plain, (![B_52, A_53, C_54]: (k1_xboole_0=B_52 | k1_tarski(A_53)=B_52 | k2_xboole_0(B_52, C_54)!=k1_tarski(A_53))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.18/1.46  tff(c_191, plain, (![A_53]: (k1_xboole_0='#skF_2' | k1_tarski(A_53)='#skF_2' | k1_tarski(A_53)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_127, c_188])).
% 3.18/1.46  tff(c_199, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_191])).
% 3.18/1.46  tff(c_208, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_151])).
% 3.18/1.46  tff(c_216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_208])).
% 3.18/1.46  tff(c_217, plain, (![A_53]: (k1_tarski(A_53)='#skF_2' | k1_tarski(A_53)!='#skF_3')), inference(splitRight, [status(thm)], [c_191])).
% 3.18/1.46  tff(c_448, plain, (![A_92]: (k1_tarski('#skF_1'(A_92))='#skF_2' | A_92!='#skF_3' | k1_xboole_0=A_92 | ~v1_zfmisc_1(A_92) | v1_xboole_0(A_92))), inference(superposition, [status(thm), theory('equality')], [c_421, c_217])).
% 3.18/1.46  tff(c_644, plain, (![A_100, C_101, B_102]: (k1_tarski('#skF_1'(A_100))=C_101 | k1_xboole_0=C_101 | k2_xboole_0(B_102, C_101)!=A_100 | k1_xboole_0=A_100 | ~v1_zfmisc_1(A_100) | v1_xboole_0(A_100))), inference(superposition, [status(thm), theory('equality')], [c_421, c_22])).
% 3.18/1.46  tff(c_646, plain, (![A_100]: (k1_tarski('#skF_1'(A_100))='#skF_3' | k1_xboole_0='#skF_3' | A_100!='#skF_3' | k1_xboole_0=A_100 | ~v1_zfmisc_1(A_100) | v1_xboole_0(A_100))), inference(superposition, [status(thm), theory('equality')], [c_127, c_644])).
% 3.18/1.46  tff(c_672, plain, (![A_105]: (k1_tarski('#skF_1'(A_105))='#skF_3' | A_105!='#skF_3' | k1_xboole_0=A_105 | ~v1_zfmisc_1(A_105) | v1_xboole_0(A_105))), inference(negUnitSimplification, [status(thm)], [c_545, c_646])).
% 3.18/1.46  tff(c_727, plain, (![A_92]: ('#skF_2'='#skF_3' | A_92!='#skF_3' | k1_xboole_0=A_92 | ~v1_zfmisc_1(A_92) | v1_xboole_0(A_92) | A_92!='#skF_3' | k1_xboole_0=A_92 | ~v1_zfmisc_1(A_92) | v1_xboole_0(A_92))), inference(superposition, [status(thm), theory('equality')], [c_448, c_672])).
% 3.18/1.46  tff(c_747, plain, (![A_106]: (A_106!='#skF_3' | k1_xboole_0=A_106 | ~v1_zfmisc_1(A_106) | v1_xboole_0(A_106) | A_106!='#skF_3' | k1_xboole_0=A_106 | ~v1_zfmisc_1(A_106) | v1_xboole_0(A_106))), inference(negUnitSimplification, [status(thm)], [c_48, c_727])).
% 3.18/1.46  tff(c_749, plain, (k1_xboole_0='#skF_3' | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_747])).
% 3.18/1.46  tff(c_752, plain, (k1_xboole_0='#skF_3' | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_749])).
% 3.18/1.46  tff(c_754, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_545, c_752])).
% 3.18/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.46  
% 3.18/1.46  Inference rules
% 3.18/1.46  ----------------------
% 3.18/1.46  #Ref     : 6
% 3.18/1.46  #Sup     : 176
% 3.18/1.46  #Fact    : 0
% 3.18/1.46  #Define  : 0
% 3.18/1.46  #Split   : 2
% 3.18/1.46  #Chain   : 0
% 3.18/1.46  #Close   : 0
% 3.18/1.46  
% 3.18/1.46  Ordering : KBO
% 3.18/1.46  
% 3.18/1.46  Simplification rules
% 3.18/1.46  ----------------------
% 3.18/1.46  #Subsume      : 24
% 3.18/1.46  #Demod        : 57
% 3.18/1.46  #Tautology    : 69
% 3.18/1.46  #SimpNegUnit  : 14
% 3.18/1.46  #BackRed      : 27
% 3.18/1.46  
% 3.18/1.46  #Partial instantiations: 0
% 3.18/1.46  #Strategies tried      : 1
% 3.18/1.46  
% 3.18/1.46  Timing (in seconds)
% 3.18/1.46  ----------------------
% 3.18/1.47  Preprocessing        : 0.31
% 3.18/1.47  Parsing              : 0.16
% 3.18/1.47  CNF conversion       : 0.02
% 3.18/1.47  Main loop            : 0.38
% 3.18/1.47  Inferencing          : 0.12
% 3.18/1.47  Reduction            : 0.10
% 3.18/1.47  Demodulation         : 0.07
% 3.18/1.47  BG Simplification    : 0.02
% 3.18/1.47  Subsumption          : 0.10
% 3.18/1.47  Abstraction          : 0.02
% 3.18/1.47  MUC search           : 0.00
% 3.18/1.47  Cooper               : 0.00
% 3.18/1.47  Total                : 0.72
% 3.18/1.47  Index Insertion      : 0.00
% 3.18/1.47  Index Deletion       : 0.00
% 3.18/1.47  Index Matching       : 0.00
% 3.18/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------

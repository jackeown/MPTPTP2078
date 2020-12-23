%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:32 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 148 expanded)
%              Number of leaves         :   27 (  61 expanded)
%              Depth                    :   12
%              Number of atoms          :  122 ( 302 expanded)
%              Number of equality atoms :   20 (  38 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_94,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_56,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_subset_1(B,A)
           => ~ v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_subset_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [C_7] : r2_hidden(C_7,k1_tarski(C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_28,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_78,plain,(
    ! [C_40,B_41,A_42] :
      ( ~ v1_xboole_0(C_40)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(C_40))
      | ~ r2_hidden(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_139,plain,(
    ! [B_49,A_50,A_51] :
      ( ~ v1_xboole_0(B_49)
      | ~ r2_hidden(A_50,A_51)
      | ~ r1_tarski(A_51,B_49) ) ),
    inference(resolution,[status(thm)],[c_28,c_78])).

tff(c_165,plain,(
    ! [B_55,C_56] :
      ( ~ v1_xboole_0(B_55)
      | ~ r1_tarski(k1_tarski(C_56),B_55) ) ),
    inference(resolution,[status(thm)],[c_10,c_139])).

tff(c_174,plain,(
    ! [C_56] : ~ v1_xboole_0(k1_tarski(C_56)) ),
    inference(resolution,[status(thm)],[c_6,c_165])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_38,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_42,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_85,plain,(
    ! [A_43,B_44] :
      ( k6_domain_1(A_43,B_44) = k1_tarski(B_44)
      | ~ m1_subset_1(B_44,A_43)
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_94,plain,
    ( k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_85])).

tff(c_99,plain,(
    k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_94])).

tff(c_106,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(k6_domain_1(A_47,B_48),k1_zfmisc_1(A_47))
      | ~ m1_subset_1(B_48,A_47)
      | v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_117,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_106])).

tff(c_122,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_117])).

tff(c_123,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_122])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_134,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_123,c_26])).

tff(c_195,plain,(
    ! [B_62,A_63] :
      ( B_62 = A_63
      | ~ r1_tarski(A_63,B_62)
      | ~ v1_zfmisc_1(B_62)
      | v1_xboole_0(B_62)
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_201,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_134,c_195])).

tff(c_211,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | v1_xboole_0('#skF_4')
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_201])).

tff(c_212,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_44,c_211])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_137,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_134,c_2])).

tff(c_138,plain,(
    ~ r1_tarski('#skF_4',k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_216,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_138])).

tff(c_223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_216])).

tff(c_224,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_40,plain,(
    v1_subset_1(k6_domain_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_100,plain,(
    v1_subset_1(k1_tarski('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_40])).

tff(c_249,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_100])).

tff(c_24,plain,(
    ! [A_11] : m1_subset_1('#skF_3'(A_11),k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_57,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,B_35)
      | ~ m1_subset_1(A_34,k1_zfmisc_1(B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_65,plain,(
    ! [A_11] : r1_tarski('#skF_3'(A_11),A_11) ),
    inference(resolution,[status(thm)],[c_24,c_57])).

tff(c_344,plain,(
    ! [B_81,A_82] :
      ( B_81 = A_82
      | ~ r1_tarski(A_82,B_81)
      | ~ v1_zfmisc_1(B_81)
      | v1_xboole_0(B_81)
      | v1_xboole_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_359,plain,(
    ! [A_85] :
      ( '#skF_3'(A_85) = A_85
      | ~ v1_zfmisc_1(A_85)
      | v1_xboole_0(A_85)
      | v1_xboole_0('#skF_3'(A_85)) ) ),
    inference(resolution,[status(thm)],[c_65,c_344])).

tff(c_22,plain,(
    ! [A_11] : ~ v1_subset_1('#skF_3'(A_11),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_226,plain,(
    ! [B_64,A_65] :
      ( ~ v1_xboole_0(B_64)
      | v1_subset_1(B_64,A_65)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_238,plain,(
    ! [A_11] :
      ( ~ v1_xboole_0('#skF_3'(A_11))
      | v1_subset_1('#skF_3'(A_11),A_11)
      | v1_xboole_0(A_11) ) ),
    inference(resolution,[status(thm)],[c_24,c_226])).

tff(c_246,plain,(
    ! [A_11] :
      ( ~ v1_xboole_0('#skF_3'(A_11))
      | v1_xboole_0(A_11) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_238])).

tff(c_364,plain,(
    ! [A_86] :
      ( '#skF_3'(A_86) = A_86
      | ~ v1_zfmisc_1(A_86)
      | v1_xboole_0(A_86) ) ),
    inference(resolution,[status(thm)],[c_359,c_246])).

tff(c_367,plain,
    ( '#skF_3'('#skF_4') = '#skF_4'
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_364])).

tff(c_370,plain,(
    '#skF_3'('#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_367])).

tff(c_389,plain,(
    ~ v1_subset_1('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_22])).

tff(c_399,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_389])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:07:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.29  
% 2.10/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.29  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.10/1.29  
% 2.10/1.29  %Foreground sorts:
% 2.10/1.29  
% 2.10/1.29  
% 2.10/1.29  %Background operators:
% 2.10/1.29  
% 2.10/1.29  
% 2.10/1.29  %Foreground operators:
% 2.10/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.29  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.10/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.10/1.29  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.10/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.10/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.10/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.29  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.10/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.10/1.29  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.10/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.10/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.10/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.29  
% 2.38/1.30  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.38/1.30  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.38/1.30  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.38/1.30  tff(f_67, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.38/1.30  tff(f_106, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.38/1.30  tff(f_81, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.38/1.30  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.38/1.30  tff(f_94, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.38/1.30  tff(f_56, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_subset_1)).
% 2.38/1.30  tff(f_50, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_subset_1(B, A) => ~v1_xboole_0(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_subset_1)).
% 2.38/1.30  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.38/1.30  tff(c_10, plain, (![C_7]: (r2_hidden(C_7, k1_tarski(C_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.38/1.30  tff(c_28, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.38/1.30  tff(c_78, plain, (![C_40, B_41, A_42]: (~v1_xboole_0(C_40) | ~m1_subset_1(B_41, k1_zfmisc_1(C_40)) | ~r2_hidden(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.38/1.30  tff(c_139, plain, (![B_49, A_50, A_51]: (~v1_xboole_0(B_49) | ~r2_hidden(A_50, A_51) | ~r1_tarski(A_51, B_49))), inference(resolution, [status(thm)], [c_28, c_78])).
% 2.38/1.30  tff(c_165, plain, (![B_55, C_56]: (~v1_xboole_0(B_55) | ~r1_tarski(k1_tarski(C_56), B_55))), inference(resolution, [status(thm)], [c_10, c_139])).
% 2.38/1.30  tff(c_174, plain, (![C_56]: (~v1_xboole_0(k1_tarski(C_56)))), inference(resolution, [status(thm)], [c_6, c_165])).
% 2.38/1.30  tff(c_44, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.38/1.30  tff(c_38, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.38/1.30  tff(c_42, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.38/1.30  tff(c_85, plain, (![A_43, B_44]: (k6_domain_1(A_43, B_44)=k1_tarski(B_44) | ~m1_subset_1(B_44, A_43) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.38/1.30  tff(c_94, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_85])).
% 2.38/1.30  tff(c_99, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_44, c_94])).
% 2.38/1.30  tff(c_106, plain, (![A_47, B_48]: (m1_subset_1(k6_domain_1(A_47, B_48), k1_zfmisc_1(A_47)) | ~m1_subset_1(B_48, A_47) | v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.38/1.30  tff(c_117, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_99, c_106])).
% 2.38/1.30  tff(c_122, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_117])).
% 2.38/1.30  tff(c_123, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_44, c_122])).
% 2.38/1.30  tff(c_26, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.38/1.30  tff(c_134, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_123, c_26])).
% 2.38/1.30  tff(c_195, plain, (![B_62, A_63]: (B_62=A_63 | ~r1_tarski(A_63, B_62) | ~v1_zfmisc_1(B_62) | v1_xboole_0(B_62) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.38/1.30  tff(c_201, plain, (k1_tarski('#skF_5')='#skF_4' | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_134, c_195])).
% 2.38/1.30  tff(c_211, plain, (k1_tarski('#skF_5')='#skF_4' | v1_xboole_0('#skF_4') | v1_xboole_0(k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_201])).
% 2.38/1.30  tff(c_212, plain, (k1_tarski('#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_174, c_44, c_211])).
% 2.38/1.30  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.38/1.30  tff(c_137, plain, (k1_tarski('#skF_5')='#skF_4' | ~r1_tarski('#skF_4', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_134, c_2])).
% 2.38/1.30  tff(c_138, plain, (~r1_tarski('#skF_4', k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_137])).
% 2.38/1.30  tff(c_216, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_212, c_138])).
% 2.38/1.30  tff(c_223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_216])).
% 2.38/1.30  tff(c_224, plain, (k1_tarski('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_137])).
% 2.38/1.30  tff(c_40, plain, (v1_subset_1(k6_domain_1('#skF_4', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.38/1.30  tff(c_100, plain, (v1_subset_1(k1_tarski('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_40])).
% 2.38/1.30  tff(c_249, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_224, c_100])).
% 2.38/1.30  tff(c_24, plain, (![A_11]: (m1_subset_1('#skF_3'(A_11), k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.38/1.30  tff(c_57, plain, (![A_34, B_35]: (r1_tarski(A_34, B_35) | ~m1_subset_1(A_34, k1_zfmisc_1(B_35)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.38/1.30  tff(c_65, plain, (![A_11]: (r1_tarski('#skF_3'(A_11), A_11))), inference(resolution, [status(thm)], [c_24, c_57])).
% 2.38/1.30  tff(c_344, plain, (![B_81, A_82]: (B_81=A_82 | ~r1_tarski(A_82, B_81) | ~v1_zfmisc_1(B_81) | v1_xboole_0(B_81) | v1_xboole_0(A_82))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.38/1.30  tff(c_359, plain, (![A_85]: ('#skF_3'(A_85)=A_85 | ~v1_zfmisc_1(A_85) | v1_xboole_0(A_85) | v1_xboole_0('#skF_3'(A_85)))), inference(resolution, [status(thm)], [c_65, c_344])).
% 2.38/1.30  tff(c_22, plain, (![A_11]: (~v1_subset_1('#skF_3'(A_11), A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.38/1.30  tff(c_226, plain, (![B_64, A_65]: (~v1_xboole_0(B_64) | v1_subset_1(B_64, A_65) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.38/1.30  tff(c_238, plain, (![A_11]: (~v1_xboole_0('#skF_3'(A_11)) | v1_subset_1('#skF_3'(A_11), A_11) | v1_xboole_0(A_11))), inference(resolution, [status(thm)], [c_24, c_226])).
% 2.38/1.30  tff(c_246, plain, (![A_11]: (~v1_xboole_0('#skF_3'(A_11)) | v1_xboole_0(A_11))), inference(negUnitSimplification, [status(thm)], [c_22, c_238])).
% 2.38/1.30  tff(c_364, plain, (![A_86]: ('#skF_3'(A_86)=A_86 | ~v1_zfmisc_1(A_86) | v1_xboole_0(A_86))), inference(resolution, [status(thm)], [c_359, c_246])).
% 2.38/1.30  tff(c_367, plain, ('#skF_3'('#skF_4')='#skF_4' | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_38, c_364])).
% 2.38/1.30  tff(c_370, plain, ('#skF_3'('#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_44, c_367])).
% 2.38/1.30  tff(c_389, plain, (~v1_subset_1('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_370, c_22])).
% 2.38/1.30  tff(c_399, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_249, c_389])).
% 2.38/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.30  
% 2.38/1.30  Inference rules
% 2.38/1.30  ----------------------
% 2.38/1.30  #Ref     : 0
% 2.38/1.30  #Sup     : 72
% 2.38/1.30  #Fact    : 0
% 2.38/1.30  #Define  : 0
% 2.38/1.30  #Split   : 3
% 2.38/1.30  #Chain   : 0
% 2.38/1.30  #Close   : 0
% 2.38/1.30  
% 2.38/1.30  Ordering : KBO
% 2.38/1.30  
% 2.38/1.30  Simplification rules
% 2.38/1.30  ----------------------
% 2.38/1.30  #Subsume      : 12
% 2.38/1.30  #Demod        : 38
% 2.38/1.30  #Tautology    : 27
% 2.38/1.30  #SimpNegUnit  : 13
% 2.38/1.30  #BackRed      : 10
% 2.38/1.30  
% 2.38/1.30  #Partial instantiations: 0
% 2.38/1.30  #Strategies tried      : 1
% 2.38/1.30  
% 2.38/1.30  Timing (in seconds)
% 2.38/1.30  ----------------------
% 2.38/1.31  Preprocessing        : 0.30
% 2.38/1.31  Parsing              : 0.15
% 2.38/1.31  CNF conversion       : 0.02
% 2.38/1.31  Main loop            : 0.22
% 2.38/1.31  Inferencing          : 0.08
% 2.38/1.31  Reduction            : 0.07
% 2.38/1.31  Demodulation         : 0.05
% 2.38/1.31  BG Simplification    : 0.02
% 2.38/1.31  Subsumption          : 0.04
% 2.38/1.31  Abstraction          : 0.01
% 2.38/1.31  MUC search           : 0.00
% 2.38/1.31  Cooper               : 0.00
% 2.38/1.31  Total                : 0.55
% 2.38/1.31  Index Insertion      : 0.00
% 2.38/1.31  Index Deletion       : 0.00
% 2.38/1.31  Index Matching       : 0.00
% 2.38/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------

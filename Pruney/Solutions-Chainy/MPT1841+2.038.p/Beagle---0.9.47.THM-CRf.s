%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:33 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 141 expanded)
%              Number of leaves         :   28 (  60 expanded)
%              Depth                    :   12
%              Number of atoms          :  106 ( 280 expanded)
%              Number of equality atoms :   18 (  35 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_100,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_69,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_subset_1(B,A)
           => ~ v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_subset_1)).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_22,plain,(
    ! [A_15] : ~ v1_xboole_0(k1_tarski(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_40,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_44,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_150,plain,(
    ! [A_65,B_66] :
      ( k6_domain_1(A_65,B_66) = k1_tarski(B_66)
      | ~ m1_subset_1(B_66,A_65)
      | v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_159,plain,
    ( k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_150])).

tff(c_164,plain,(
    k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_159])).

tff(c_183,plain,(
    ! [A_69,B_70] :
      ( m1_subset_1(k6_domain_1(A_69,B_70),k1_zfmisc_1(A_69))
      | ~ m1_subset_1(B_70,A_69)
      | v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_192,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_183])).

tff(c_196,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_192])).

tff(c_197,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_196])).

tff(c_30,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,B_22)
      | ~ m1_subset_1(A_21,k1_zfmisc_1(B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_205,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_197,c_30])).

tff(c_364,plain,(
    ! [B_80,A_81] :
      ( B_80 = A_81
      | ~ r1_tarski(A_81,B_80)
      | ~ v1_zfmisc_1(B_80)
      | v1_xboole_0(B_80)
      | v1_xboole_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_367,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_205,c_364])).

tff(c_379,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | v1_xboole_0('#skF_4')
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_367])).

tff(c_380,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_46,c_379])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_217,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_205,c_12])).

tff(c_226,plain,(
    ~ r1_tarski('#skF_4',k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_385,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_226])).

tff(c_392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_385])).

tff(c_393,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_42,plain,(
    v1_subset_1(k6_domain_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_165,plain,(
    v1_subset_1(k1_tarski('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_42])).

tff(c_397,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_165])).

tff(c_28,plain,(
    ! [A_19] : m1_subset_1('#skF_3'(A_19),k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_68,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | ~ m1_subset_1(A_41,k1_zfmisc_1(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_76,plain,(
    ! [A_19] : r1_tarski('#skF_3'(A_19),A_19) ),
    inference(resolution,[status(thm)],[c_28,c_68])).

tff(c_599,plain,(
    ! [B_91,A_92] :
      ( B_91 = A_92
      | ~ r1_tarski(A_92,B_91)
      | ~ v1_zfmisc_1(B_91)
      | v1_xboole_0(B_91)
      | v1_xboole_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_873,plain,(
    ! [A_107] :
      ( '#skF_3'(A_107) = A_107
      | ~ v1_zfmisc_1(A_107)
      | v1_xboole_0(A_107)
      | v1_xboole_0('#skF_3'(A_107)) ) ),
    inference(resolution,[status(thm)],[c_76,c_599])).

tff(c_26,plain,(
    ! [A_19] : ~ v1_subset_1('#skF_3'(A_19),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_466,plain,(
    ! [B_85,A_86] :
      ( ~ v1_xboole_0(B_85)
      | v1_subset_1(B_85,A_86)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_86))
      | v1_xboole_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_478,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0('#skF_3'(A_19))
      | v1_subset_1('#skF_3'(A_19),A_19)
      | v1_xboole_0(A_19) ) ),
    inference(resolution,[status(thm)],[c_28,c_466])).

tff(c_486,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0('#skF_3'(A_19))
      | v1_xboole_0(A_19) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_478])).

tff(c_913,plain,(
    ! [A_108] :
      ( '#skF_3'(A_108) = A_108
      | ~ v1_zfmisc_1(A_108)
      | v1_xboole_0(A_108) ) ),
    inference(resolution,[status(thm)],[c_873,c_486])).

tff(c_916,plain,
    ( '#skF_3'('#skF_4') = '#skF_4'
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_913])).

tff(c_919,plain,(
    '#skF_3'('#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_916])).

tff(c_968,plain,(
    ~ v1_subset_1('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_919,c_26])).

tff(c_988,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_968])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:00:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.41  
% 2.71/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.41  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 2.71/1.41  
% 2.71/1.41  %Foreground sorts:
% 2.71/1.41  
% 2.71/1.41  
% 2.71/1.41  %Background operators:
% 2.71/1.41  
% 2.71/1.41  
% 2.71/1.41  %Foreground operators:
% 2.71/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.71/1.41  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.71/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.71/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.71/1.41  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.71/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.71/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.71/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.71/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.71/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.71/1.41  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.71/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.71/1.41  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.71/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.71/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.71/1.41  
% 2.71/1.42  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.71/1.42  tff(f_51, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.71/1.42  tff(f_112, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.71/1.42  tff(f_87, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.71/1.42  tff(f_80, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.71/1.42  tff(f_73, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.71/1.42  tff(f_100, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.71/1.42  tff(f_69, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 2.71/1.42  tff(f_63, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_subset_1(B, A) => ~v1_xboole_0(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_subset_1)).
% 2.71/1.42  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.71/1.42  tff(c_22, plain, (![A_15]: (~v1_xboole_0(k1_tarski(A_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.71/1.42  tff(c_46, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.71/1.42  tff(c_40, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.71/1.42  tff(c_44, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.71/1.42  tff(c_150, plain, (![A_65, B_66]: (k6_domain_1(A_65, B_66)=k1_tarski(B_66) | ~m1_subset_1(B_66, A_65) | v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.71/1.42  tff(c_159, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_150])).
% 2.71/1.42  tff(c_164, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_46, c_159])).
% 2.71/1.42  tff(c_183, plain, (![A_69, B_70]: (m1_subset_1(k6_domain_1(A_69, B_70), k1_zfmisc_1(A_69)) | ~m1_subset_1(B_70, A_69) | v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.71/1.42  tff(c_192, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_164, c_183])).
% 2.71/1.42  tff(c_196, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_192])).
% 2.71/1.42  tff(c_197, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_46, c_196])).
% 2.71/1.42  tff(c_30, plain, (![A_21, B_22]: (r1_tarski(A_21, B_22) | ~m1_subset_1(A_21, k1_zfmisc_1(B_22)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.71/1.42  tff(c_205, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_197, c_30])).
% 2.71/1.42  tff(c_364, plain, (![B_80, A_81]: (B_80=A_81 | ~r1_tarski(A_81, B_80) | ~v1_zfmisc_1(B_80) | v1_xboole_0(B_80) | v1_xboole_0(A_81))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.71/1.42  tff(c_367, plain, (k1_tarski('#skF_5')='#skF_4' | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_205, c_364])).
% 2.71/1.42  tff(c_379, plain, (k1_tarski('#skF_5')='#skF_4' | v1_xboole_0('#skF_4') | v1_xboole_0(k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_367])).
% 2.71/1.42  tff(c_380, plain, (k1_tarski('#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_22, c_46, c_379])).
% 2.71/1.42  tff(c_12, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.71/1.42  tff(c_217, plain, (k1_tarski('#skF_5')='#skF_4' | ~r1_tarski('#skF_4', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_205, c_12])).
% 2.71/1.42  tff(c_226, plain, (~r1_tarski('#skF_4', k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_217])).
% 2.71/1.42  tff(c_385, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_380, c_226])).
% 2.71/1.42  tff(c_392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_385])).
% 2.71/1.42  tff(c_393, plain, (k1_tarski('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_217])).
% 2.71/1.42  tff(c_42, plain, (v1_subset_1(k6_domain_1('#skF_4', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.71/1.42  tff(c_165, plain, (v1_subset_1(k1_tarski('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_42])).
% 2.71/1.42  tff(c_397, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_393, c_165])).
% 2.71/1.42  tff(c_28, plain, (![A_19]: (m1_subset_1('#skF_3'(A_19), k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.71/1.42  tff(c_68, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | ~m1_subset_1(A_41, k1_zfmisc_1(B_42)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.71/1.42  tff(c_76, plain, (![A_19]: (r1_tarski('#skF_3'(A_19), A_19))), inference(resolution, [status(thm)], [c_28, c_68])).
% 2.71/1.42  tff(c_599, plain, (![B_91, A_92]: (B_91=A_92 | ~r1_tarski(A_92, B_91) | ~v1_zfmisc_1(B_91) | v1_xboole_0(B_91) | v1_xboole_0(A_92))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.71/1.42  tff(c_873, plain, (![A_107]: ('#skF_3'(A_107)=A_107 | ~v1_zfmisc_1(A_107) | v1_xboole_0(A_107) | v1_xboole_0('#skF_3'(A_107)))), inference(resolution, [status(thm)], [c_76, c_599])).
% 2.71/1.42  tff(c_26, plain, (![A_19]: (~v1_subset_1('#skF_3'(A_19), A_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.71/1.42  tff(c_466, plain, (![B_85, A_86]: (~v1_xboole_0(B_85) | v1_subset_1(B_85, A_86) | ~m1_subset_1(B_85, k1_zfmisc_1(A_86)) | v1_xboole_0(A_86))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.71/1.42  tff(c_478, plain, (![A_19]: (~v1_xboole_0('#skF_3'(A_19)) | v1_subset_1('#skF_3'(A_19), A_19) | v1_xboole_0(A_19))), inference(resolution, [status(thm)], [c_28, c_466])).
% 2.71/1.42  tff(c_486, plain, (![A_19]: (~v1_xboole_0('#skF_3'(A_19)) | v1_xboole_0(A_19))), inference(negUnitSimplification, [status(thm)], [c_26, c_478])).
% 2.71/1.42  tff(c_913, plain, (![A_108]: ('#skF_3'(A_108)=A_108 | ~v1_zfmisc_1(A_108) | v1_xboole_0(A_108))), inference(resolution, [status(thm)], [c_873, c_486])).
% 2.71/1.42  tff(c_916, plain, ('#skF_3'('#skF_4')='#skF_4' | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_913])).
% 2.71/1.42  tff(c_919, plain, ('#skF_3'('#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_46, c_916])).
% 2.71/1.42  tff(c_968, plain, (~v1_subset_1('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_919, c_26])).
% 2.71/1.42  tff(c_988, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_397, c_968])).
% 2.71/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.42  
% 2.71/1.42  Inference rules
% 2.71/1.42  ----------------------
% 2.71/1.42  #Ref     : 0
% 2.71/1.42  #Sup     : 217
% 2.71/1.42  #Fact    : 0
% 2.71/1.42  #Define  : 0
% 2.71/1.42  #Split   : 3
% 2.71/1.42  #Chain   : 0
% 2.71/1.42  #Close   : 0
% 2.71/1.42  
% 2.71/1.42  Ordering : KBO
% 2.71/1.42  
% 2.71/1.42  Simplification rules
% 2.71/1.42  ----------------------
% 2.71/1.42  #Subsume      : 58
% 2.71/1.42  #Demod        : 123
% 2.71/1.42  #Tautology    : 85
% 2.71/1.42  #SimpNegUnit  : 14
% 2.71/1.42  #BackRed      : 10
% 2.71/1.42  
% 2.71/1.42  #Partial instantiations: 0
% 2.71/1.42  #Strategies tried      : 1
% 2.71/1.42  
% 2.71/1.42  Timing (in seconds)
% 2.71/1.42  ----------------------
% 2.71/1.43  Preprocessing        : 0.31
% 2.71/1.43  Parsing              : 0.16
% 2.71/1.43  CNF conversion       : 0.02
% 2.71/1.43  Main loop            : 0.35
% 2.71/1.43  Inferencing          : 0.13
% 2.71/1.43  Reduction            : 0.10
% 2.71/1.43  Demodulation         : 0.07
% 2.71/1.43  BG Simplification    : 0.02
% 2.71/1.43  Subsumption          : 0.08
% 2.71/1.43  Abstraction          : 0.02
% 2.71/1.43  MUC search           : 0.00
% 2.71/1.43  Cooper               : 0.00
% 2.71/1.43  Total                : 0.69
% 2.71/1.43  Index Insertion      : 0.00
% 2.71/1.43  Index Deletion       : 0.00
% 2.71/1.43  Index Matching       : 0.00
% 2.71/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------

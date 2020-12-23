%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:47 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 113 expanded)
%              Number of leaves         :   33 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :   85 ( 206 expanded)
%              Number of equality atoms :   19 (  32 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_51,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_54,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_85,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(c_20,plain,(
    ! [A_18] : k2_subset_1(A_18) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_19] : ~ v1_subset_1(k2_subset_1(A_19),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_41,plain,(
    ! [A_19] : ~ v1_subset_1(A_19,A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_34,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_38,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_144,plain,(
    ! [A_65,B_66] :
      ( k6_domain_1(A_65,B_66) = k1_tarski(B_66)
      | ~ m1_subset_1(B_66,A_65)
      | v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_150,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_144])).

tff(c_154,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_150])).

tff(c_28,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(k6_domain_1(A_22,B_23),k1_zfmisc_1(A_22))
      | ~ m1_subset_1(B_23,A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_168,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_28])).

tff(c_172,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_168])).

tff(c_173,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_172])).

tff(c_24,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_182,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_173,c_24])).

tff(c_212,plain,(
    ! [B_71,A_72] :
      ( B_71 = A_72
      | ~ r1_tarski(A_72,B_71)
      | ~ v1_zfmisc_1(B_71)
      | v1_xboole_0(B_71)
      | v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_218,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_182,c_212])).

tff(c_228,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_218])).

tff(c_229,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_228])).

tff(c_233,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_229])).

tff(c_85,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_2'(A_49,B_50),A_49)
      | r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_121,plain,(
    ! [A_57,B_58] :
      ( ~ v1_xboole_0(A_57)
      | r1_tarski(A_57,B_58) ) ),
    inference(resolution,[status(thm)],[c_85,c_2])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( k2_xboole_0(A_12,B_13) = B_13
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_125,plain,(
    ! [A_57,B_58] :
      ( k2_xboole_0(A_57,B_58) = B_58
      | ~ v1_xboole_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_121,c_14])).

tff(c_251,plain,(
    ! [B_76] : k2_xboole_0(k1_tarski('#skF_4'),B_76) = B_76 ),
    inference(resolution,[status(thm)],[c_233,c_125])).

tff(c_18,plain,(
    ! [A_16,B_17] : k2_xboole_0(k1_tarski(A_16),B_17) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_260,plain,(
    ! [B_76] : k1_xboole_0 != B_76 ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_18])).

tff(c_275,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_260])).

tff(c_276,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_229])).

tff(c_36,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_164,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_36])).

tff(c_281,plain,(
    v1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_164])).

tff(c_286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_281])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:55:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.40  
% 2.29/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.40  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.29/1.40  
% 2.29/1.40  %Foreground sorts:
% 2.29/1.40  
% 2.29/1.40  
% 2.29/1.40  %Background operators:
% 2.29/1.40  
% 2.29/1.40  
% 2.29/1.40  %Foreground operators:
% 2.29/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.29/1.40  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.29/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.29/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.29/1.40  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.29/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.29/1.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.29/1.40  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.29/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.29/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.29/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.29/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.29/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.29/1.40  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.29/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.29/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.29/1.40  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.29/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.29/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.29/1.40  
% 2.29/1.41  tff(f_51, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.29/1.41  tff(f_54, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_subset_1)).
% 2.29/1.41  tff(f_97, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.29/1.41  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.29/1.41  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.29/1.41  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.29/1.41  tff(f_85, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.29/1.41  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.29/1.41  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.29/1.41  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.29/1.41  tff(f_49, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.29/1.41  tff(c_20, plain, (![A_18]: (k2_subset_1(A_18)=A_18)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.29/1.41  tff(c_22, plain, (![A_19]: (~v1_subset_1(k2_subset_1(A_19), A_19))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.29/1.41  tff(c_41, plain, (![A_19]: (~v1_subset_1(A_19, A_19))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 2.29/1.41  tff(c_40, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.29/1.41  tff(c_34, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.29/1.41  tff(c_38, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.29/1.41  tff(c_144, plain, (![A_65, B_66]: (k6_domain_1(A_65, B_66)=k1_tarski(B_66) | ~m1_subset_1(B_66, A_65) | v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.29/1.41  tff(c_150, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_144])).
% 2.29/1.41  tff(c_154, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_40, c_150])).
% 2.29/1.41  tff(c_28, plain, (![A_22, B_23]: (m1_subset_1(k6_domain_1(A_22, B_23), k1_zfmisc_1(A_22)) | ~m1_subset_1(B_23, A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.29/1.41  tff(c_168, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_154, c_28])).
% 2.29/1.41  tff(c_172, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_168])).
% 2.29/1.41  tff(c_173, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_40, c_172])).
% 2.29/1.41  tff(c_24, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~m1_subset_1(A_20, k1_zfmisc_1(B_21)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.29/1.41  tff(c_182, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_173, c_24])).
% 2.29/1.41  tff(c_212, plain, (![B_71, A_72]: (B_71=A_72 | ~r1_tarski(A_72, B_71) | ~v1_zfmisc_1(B_71) | v1_xboole_0(B_71) | v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.29/1.41  tff(c_218, plain, (k1_tarski('#skF_4')='#skF_3' | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | v1_xboole_0(k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_182, c_212])).
% 2.29/1.41  tff(c_228, plain, (k1_tarski('#skF_4')='#skF_3' | v1_xboole_0('#skF_3') | v1_xboole_0(k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_218])).
% 2.29/1.41  tff(c_229, plain, (k1_tarski('#skF_4')='#skF_3' | v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_40, c_228])).
% 2.29/1.41  tff(c_233, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_229])).
% 2.29/1.41  tff(c_85, plain, (![A_49, B_50]: (r2_hidden('#skF_2'(A_49, B_50), A_49) | r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.29/1.41  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.29/1.41  tff(c_121, plain, (![A_57, B_58]: (~v1_xboole_0(A_57) | r1_tarski(A_57, B_58))), inference(resolution, [status(thm)], [c_85, c_2])).
% 2.29/1.41  tff(c_14, plain, (![A_12, B_13]: (k2_xboole_0(A_12, B_13)=B_13 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.29/1.41  tff(c_125, plain, (![A_57, B_58]: (k2_xboole_0(A_57, B_58)=B_58 | ~v1_xboole_0(A_57))), inference(resolution, [status(thm)], [c_121, c_14])).
% 2.29/1.41  tff(c_251, plain, (![B_76]: (k2_xboole_0(k1_tarski('#skF_4'), B_76)=B_76)), inference(resolution, [status(thm)], [c_233, c_125])).
% 2.29/1.41  tff(c_18, plain, (![A_16, B_17]: (k2_xboole_0(k1_tarski(A_16), B_17)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.29/1.41  tff(c_260, plain, (![B_76]: (k1_xboole_0!=B_76)), inference(superposition, [status(thm), theory('equality')], [c_251, c_18])).
% 2.29/1.41  tff(c_275, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_260])).
% 2.29/1.41  tff(c_276, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_229])).
% 2.29/1.41  tff(c_36, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.29/1.41  tff(c_164, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_36])).
% 2.29/1.41  tff(c_281, plain, (v1_subset_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_276, c_164])).
% 2.29/1.41  tff(c_286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41, c_281])).
% 2.29/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.41  
% 2.29/1.41  Inference rules
% 2.29/1.41  ----------------------
% 2.29/1.41  #Ref     : 1
% 2.29/1.41  #Sup     : 51
% 2.29/1.41  #Fact    : 0
% 2.29/1.41  #Define  : 0
% 2.29/1.41  #Split   : 1
% 2.29/1.41  #Chain   : 0
% 2.29/1.41  #Close   : 0
% 2.29/1.41  
% 2.29/1.41  Ordering : KBO
% 2.29/1.41  
% 2.29/1.41  Simplification rules
% 2.29/1.41  ----------------------
% 2.29/1.41  #Subsume      : 4
% 2.29/1.41  #Demod        : 14
% 2.29/1.41  #Tautology    : 28
% 2.29/1.41  #SimpNegUnit  : 5
% 2.29/1.41  #BackRed      : 6
% 2.29/1.41  
% 2.29/1.41  #Partial instantiations: 0
% 2.29/1.41  #Strategies tried      : 1
% 2.29/1.41  
% 2.29/1.41  Timing (in seconds)
% 2.29/1.41  ----------------------
% 2.29/1.42  Preprocessing        : 0.43
% 2.29/1.42  Parsing              : 0.26
% 2.29/1.42  CNF conversion       : 0.02
% 2.29/1.42  Main loop            : 0.19
% 2.29/1.42  Inferencing          : 0.08
% 2.29/1.42  Reduction            : 0.05
% 2.29/1.42  Demodulation         : 0.04
% 2.29/1.42  BG Simplification    : 0.01
% 2.29/1.42  Subsumption          : 0.03
% 2.29/1.42  Abstraction          : 0.01
% 2.29/1.42  MUC search           : 0.00
% 2.29/1.42  Cooper               : 0.00
% 2.29/1.42  Total                : 0.65
% 2.29/1.42  Index Insertion      : 0.00
% 2.29/1.42  Index Deletion       : 0.00
% 2.29/1.42  Index Matching       : 0.00
% 2.29/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------

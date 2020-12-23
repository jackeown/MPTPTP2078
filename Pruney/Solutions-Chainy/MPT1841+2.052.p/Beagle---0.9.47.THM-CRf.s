%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:35 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   65 (  83 expanded)
%              Number of leaves         :   31 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :   89 ( 138 expanded)
%              Number of equality atoms :   18 (  23 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_46,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_57,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(c_18,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_118,plain,(
    ! [A_48,B_49] :
      ( k2_xboole_0(A_48,B_49) = B_49
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_123,plain,(
    ! [B_50] : k2_xboole_0(B_50,B_50) = B_50 ),
    inference(resolution,[status(thm)],[c_18,c_118])).

tff(c_68,plain,(
    ! [B_44,A_45] : k2_xboole_0(B_44,A_45) = k2_xboole_0(A_45,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_17,B_18] : k2_xboole_0(k1_tarski(A_17),B_18) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_84,plain,(
    ! [B_44,A_17] : k2_xboole_0(B_44,k1_tarski(A_17)) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_24])).

tff(c_130,plain,(
    ! [A_17] : k1_tarski(A_17) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_84])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_42,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_46,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_342,plain,(
    ! [A_85,B_86] :
      ( k6_domain_1(A_85,B_86) = k1_tarski(B_86)
      | ~ m1_subset_1(B_86,A_85)
      | v1_xboole_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_351,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_342])).

tff(c_356,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_351])).

tff(c_44,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_357,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_44])).

tff(c_713,plain,(
    ! [A_125,B_126] :
      ( m1_subset_1(k6_domain_1(A_125,B_126),k1_zfmisc_1(A_125))
      | ~ m1_subset_1(B_126,A_125)
      | v1_xboole_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_730,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_713])).

tff(c_738,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_730])).

tff(c_739,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_738])).

tff(c_815,plain,(
    ! [B_128,A_129] :
      ( ~ v1_subset_1(B_128,A_129)
      | v1_xboole_0(B_128)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(A_129))
      | ~ v1_zfmisc_1(A_129)
      | v1_xboole_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_818,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4'))
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_739,c_815])).

tff(c_838,plain,
    ( v1_xboole_0(k1_tarski('#skF_4'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_357,c_818])).

tff(c_839,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_838])).

tff(c_151,plain,(
    ! [A_56,B_57] :
      ( r2_hidden('#skF_2'(A_56,B_57),A_56)
      | r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_155,plain,(
    ! [A_56,B_57] :
      ( ~ v1_xboole_0(A_56)
      | r1_tarski(A_56,B_57) ) ),
    inference(resolution,[status(thm)],[c_151,c_4])).

tff(c_26,plain,(
    ! [A_19] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_142,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | ~ m1_subset_1(A_54,k1_zfmisc_1(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_150,plain,(
    ! [A_19] : r1_tarski(k1_xboole_0,A_19) ),
    inference(resolution,[status(thm)],[c_26,c_142])).

tff(c_265,plain,(
    ! [B_67,A_68] :
      ( B_67 = A_68
      | ~ r1_tarski(B_67,A_68)
      | ~ r1_tarski(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_278,plain,(
    ! [A_69] :
      ( k1_xboole_0 = A_69
      | ~ r1_tarski(A_69,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_150,c_265])).

tff(c_291,plain,(
    ! [A_56] :
      ( k1_xboole_0 = A_56
      | ~ v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_155,c_278])).

tff(c_850,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_839,c_291])).

tff(c_857,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_850])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:37:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.40  
% 2.79/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.40  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.79/1.40  
% 2.79/1.40  %Foreground sorts:
% 2.79/1.40  
% 2.79/1.40  
% 2.79/1.40  %Background operators:
% 2.79/1.40  
% 2.79/1.40  
% 2.79/1.40  %Foreground operators:
% 2.79/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.79/1.40  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.79/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.79/1.40  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.79/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.79/1.40  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.79/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.79/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.79/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.79/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.79/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.79/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.79/1.40  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.79/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.79/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.79/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.79/1.40  
% 2.79/1.42  tff(f_46, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.79/1.42  tff(f_50, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.79/1.42  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.79/1.42  tff(f_55, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.79/1.42  tff(f_115, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.79/1.42  tff(f_89, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.79/1.42  tff(f_82, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.79/1.42  tff(f_103, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.79/1.42  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.79/1.42  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.79/1.42  tff(f_57, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.79/1.42  tff(f_69, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.79/1.42  tff(c_18, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.79/1.42  tff(c_118, plain, (![A_48, B_49]: (k2_xboole_0(A_48, B_49)=B_49 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.79/1.42  tff(c_123, plain, (![B_50]: (k2_xboole_0(B_50, B_50)=B_50)), inference(resolution, [status(thm)], [c_18, c_118])).
% 2.79/1.42  tff(c_68, plain, (![B_44, A_45]: (k2_xboole_0(B_44, A_45)=k2_xboole_0(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.79/1.42  tff(c_24, plain, (![A_17, B_18]: (k2_xboole_0(k1_tarski(A_17), B_18)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.79/1.42  tff(c_84, plain, (![B_44, A_17]: (k2_xboole_0(B_44, k1_tarski(A_17))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_68, c_24])).
% 2.79/1.42  tff(c_130, plain, (![A_17]: (k1_tarski(A_17)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_123, c_84])).
% 2.79/1.42  tff(c_48, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.79/1.42  tff(c_42, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.79/1.42  tff(c_46, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.79/1.42  tff(c_342, plain, (![A_85, B_86]: (k6_domain_1(A_85, B_86)=k1_tarski(B_86) | ~m1_subset_1(B_86, A_85) | v1_xboole_0(A_85))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.79/1.42  tff(c_351, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_342])).
% 2.79/1.42  tff(c_356, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_48, c_351])).
% 2.79/1.42  tff(c_44, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.79/1.42  tff(c_357, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_356, c_44])).
% 2.79/1.42  tff(c_713, plain, (![A_125, B_126]: (m1_subset_1(k6_domain_1(A_125, B_126), k1_zfmisc_1(A_125)) | ~m1_subset_1(B_126, A_125) | v1_xboole_0(A_125))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.79/1.42  tff(c_730, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_356, c_713])).
% 2.79/1.42  tff(c_738, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_730])).
% 2.79/1.42  tff(c_739, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_738])).
% 2.79/1.42  tff(c_815, plain, (![B_128, A_129]: (~v1_subset_1(B_128, A_129) | v1_xboole_0(B_128) | ~m1_subset_1(B_128, k1_zfmisc_1(A_129)) | ~v1_zfmisc_1(A_129) | v1_xboole_0(A_129))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.79/1.42  tff(c_818, plain, (~v1_subset_1(k1_tarski('#skF_4'), '#skF_3') | v1_xboole_0(k1_tarski('#skF_4')) | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_739, c_815])).
% 2.79/1.42  tff(c_838, plain, (v1_xboole_0(k1_tarski('#skF_4')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_357, c_818])).
% 2.79/1.42  tff(c_839, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_48, c_838])).
% 2.79/1.42  tff(c_151, plain, (![A_56, B_57]: (r2_hidden('#skF_2'(A_56, B_57), A_56) | r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.79/1.42  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.79/1.42  tff(c_155, plain, (![A_56, B_57]: (~v1_xboole_0(A_56) | r1_tarski(A_56, B_57))), inference(resolution, [status(thm)], [c_151, c_4])).
% 2.79/1.42  tff(c_26, plain, (![A_19]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.79/1.42  tff(c_142, plain, (![A_54, B_55]: (r1_tarski(A_54, B_55) | ~m1_subset_1(A_54, k1_zfmisc_1(B_55)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.79/1.42  tff(c_150, plain, (![A_19]: (r1_tarski(k1_xboole_0, A_19))), inference(resolution, [status(thm)], [c_26, c_142])).
% 2.79/1.42  tff(c_265, plain, (![B_67, A_68]: (B_67=A_68 | ~r1_tarski(B_67, A_68) | ~r1_tarski(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.79/1.42  tff(c_278, plain, (![A_69]: (k1_xboole_0=A_69 | ~r1_tarski(A_69, k1_xboole_0))), inference(resolution, [status(thm)], [c_150, c_265])).
% 2.79/1.42  tff(c_291, plain, (![A_56]: (k1_xboole_0=A_56 | ~v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_155, c_278])).
% 2.79/1.42  tff(c_850, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_839, c_291])).
% 2.79/1.42  tff(c_857, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_850])).
% 2.79/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.42  
% 2.79/1.42  Inference rules
% 2.79/1.42  ----------------------
% 2.79/1.42  #Ref     : 0
% 2.79/1.42  #Sup     : 187
% 2.79/1.42  #Fact    : 0
% 2.79/1.42  #Define  : 0
% 2.79/1.42  #Split   : 1
% 2.79/1.42  #Chain   : 0
% 2.79/1.42  #Close   : 0
% 2.79/1.42  
% 2.79/1.42  Ordering : KBO
% 2.79/1.42  
% 2.79/1.42  Simplification rules
% 2.79/1.42  ----------------------
% 2.79/1.42  #Subsume      : 28
% 2.79/1.42  #Demod        : 40
% 2.79/1.42  #Tautology    : 73
% 2.79/1.42  #SimpNegUnit  : 10
% 2.79/1.42  #BackRed      : 6
% 2.79/1.42  
% 2.79/1.42  #Partial instantiations: 0
% 2.79/1.42  #Strategies tried      : 1
% 2.79/1.42  
% 2.79/1.42  Timing (in seconds)
% 2.79/1.42  ----------------------
% 2.79/1.42  Preprocessing        : 0.32
% 2.79/1.42  Parsing              : 0.17
% 2.79/1.42  CNF conversion       : 0.02
% 2.79/1.42  Main loop            : 0.33
% 2.79/1.42  Inferencing          : 0.12
% 2.79/1.42  Reduction            : 0.10
% 2.79/1.42  Demodulation         : 0.07
% 2.79/1.42  BG Simplification    : 0.02
% 2.79/1.42  Subsumption          : 0.07
% 2.79/1.42  Abstraction          : 0.02
% 2.79/1.42  MUC search           : 0.00
% 2.79/1.42  Cooper               : 0.00
% 2.79/1.42  Total                : 0.68
% 2.79/1.42  Index Insertion      : 0.00
% 2.79/1.42  Index Deletion       : 0.00
% 2.79/1.42  Index Matching       : 0.00
% 2.79/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------

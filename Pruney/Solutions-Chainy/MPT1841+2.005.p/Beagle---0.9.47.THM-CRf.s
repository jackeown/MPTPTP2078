%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:28 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :   63 (  80 expanded)
%              Number of leaves         :   33 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :   82 ( 128 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_48,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

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

tff(f_57,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_20,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_72,plain,(
    ! [A_41,B_42] : k2_xboole_0(k1_tarski(A_41),B_42) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_76,plain,(
    ! [A_41] : k1_tarski(A_41) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_72])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_44,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_48,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_440,plain,(
    ! [A_109,B_110] :
      ( k6_domain_1(A_109,B_110) = k1_tarski(B_110)
      | ~ m1_subset_1(B_110,A_109)
      | v1_xboole_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_449,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_440])).

tff(c_454,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_449])).

tff(c_46,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_455,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_46])).

tff(c_509,plain,(
    ! [A_121,B_122] :
      ( m1_subset_1(k6_domain_1(A_121,B_122),k1_zfmisc_1(A_121))
      | ~ m1_subset_1(B_122,A_121)
      | v1_xboole_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_526,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_454,c_509])).

tff(c_534,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_526])).

tff(c_535,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_534])).

tff(c_832,plain,(
    ! [B_133,A_134] :
      ( ~ v1_subset_1(B_133,A_134)
      | v1_xboole_0(B_133)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(A_134))
      | ~ v1_zfmisc_1(A_134)
      | v1_xboole_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_838,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4'))
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_535,c_832])).

tff(c_853,plain,
    ( v1_xboole_0(k1_tarski('#skF_4'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_455,c_838])).

tff(c_854,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_853])).

tff(c_377,plain,(
    ! [A_95,B_96] :
      ( r2_hidden('#skF_2'(A_95,B_96),A_95)
      | r1_tarski(A_95,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_388,plain,(
    ! [A_97,B_98] :
      ( ~ v1_xboole_0(A_97)
      | r1_tarski(A_97,B_98) ) ),
    inference(resolution,[status(thm)],[c_377,c_2])).

tff(c_28,plain,(
    ! [A_20] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_85,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_93,plain,(
    ! [A_20] : r1_tarski(k1_xboole_0,A_20) ),
    inference(resolution,[status(thm)],[c_28,c_85])).

tff(c_343,plain,(
    ! [B_88,A_89] :
      ( B_88 = A_89
      | ~ r1_tarski(B_88,A_89)
      | ~ r1_tarski(A_89,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_348,plain,(
    ! [A_20] :
      ( k1_xboole_0 = A_20
      | ~ r1_tarski(A_20,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_93,c_343])).

tff(c_399,plain,(
    ! [A_97] :
      ( k1_xboole_0 = A_97
      | ~ v1_xboole_0(A_97) ) ),
    inference(resolution,[status(thm)],[c_388,c_348])).

tff(c_863,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_854,c_399])).

tff(c_868,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_863])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:05:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.42  
% 2.78/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.42  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.78/1.42  
% 2.78/1.42  %Foreground sorts:
% 2.78/1.42  
% 2.78/1.42  
% 2.78/1.42  %Background operators:
% 2.78/1.42  
% 2.78/1.42  
% 2.78/1.42  %Foreground operators:
% 2.78/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.78/1.42  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.78/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.78/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.78/1.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.78/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.78/1.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.78/1.42  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.78/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.78/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.78/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.78/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.78/1.42  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.78/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.78/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.78/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.78/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.78/1.42  
% 3.03/1.43  tff(f_48, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.03/1.43  tff(f_55, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.03/1.43  tff(f_114, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 3.03/1.43  tff(f_88, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.03/1.43  tff(f_81, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.03/1.43  tff(f_102, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 3.03/1.43  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.03/1.43  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.03/1.43  tff(f_57, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.03/1.43  tff(f_68, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.03/1.43  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.03/1.43  tff(c_20, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.03/1.43  tff(c_72, plain, (![A_41, B_42]: (k2_xboole_0(k1_tarski(A_41), B_42)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.03/1.43  tff(c_76, plain, (![A_41]: (k1_tarski(A_41)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_72])).
% 3.03/1.43  tff(c_50, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.03/1.43  tff(c_44, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.03/1.43  tff(c_48, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.03/1.43  tff(c_440, plain, (![A_109, B_110]: (k6_domain_1(A_109, B_110)=k1_tarski(B_110) | ~m1_subset_1(B_110, A_109) | v1_xboole_0(A_109))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.03/1.43  tff(c_449, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_440])).
% 3.03/1.43  tff(c_454, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_50, c_449])).
% 3.03/1.43  tff(c_46, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.03/1.43  tff(c_455, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_454, c_46])).
% 3.03/1.43  tff(c_509, plain, (![A_121, B_122]: (m1_subset_1(k6_domain_1(A_121, B_122), k1_zfmisc_1(A_121)) | ~m1_subset_1(B_122, A_121) | v1_xboole_0(A_121))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.03/1.43  tff(c_526, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_454, c_509])).
% 3.03/1.43  tff(c_534, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_526])).
% 3.03/1.43  tff(c_535, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_534])).
% 3.03/1.43  tff(c_832, plain, (![B_133, A_134]: (~v1_subset_1(B_133, A_134) | v1_xboole_0(B_133) | ~m1_subset_1(B_133, k1_zfmisc_1(A_134)) | ~v1_zfmisc_1(A_134) | v1_xboole_0(A_134))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.03/1.43  tff(c_838, plain, (~v1_subset_1(k1_tarski('#skF_4'), '#skF_3') | v1_xboole_0(k1_tarski('#skF_4')) | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_535, c_832])).
% 3.03/1.43  tff(c_853, plain, (v1_xboole_0(k1_tarski('#skF_4')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_455, c_838])).
% 3.03/1.43  tff(c_854, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_50, c_853])).
% 3.03/1.43  tff(c_377, plain, (![A_95, B_96]: (r2_hidden('#skF_2'(A_95, B_96), A_95) | r1_tarski(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.03/1.43  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.03/1.43  tff(c_388, plain, (![A_97, B_98]: (~v1_xboole_0(A_97) | r1_tarski(A_97, B_98))), inference(resolution, [status(thm)], [c_377, c_2])).
% 3.03/1.43  tff(c_28, plain, (![A_20]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.03/1.43  tff(c_85, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.03/1.43  tff(c_93, plain, (![A_20]: (r1_tarski(k1_xboole_0, A_20))), inference(resolution, [status(thm)], [c_28, c_85])).
% 3.03/1.43  tff(c_343, plain, (![B_88, A_89]: (B_88=A_89 | ~r1_tarski(B_88, A_89) | ~r1_tarski(A_89, B_88))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.03/1.43  tff(c_348, plain, (![A_20]: (k1_xboole_0=A_20 | ~r1_tarski(A_20, k1_xboole_0))), inference(resolution, [status(thm)], [c_93, c_343])).
% 3.03/1.43  tff(c_399, plain, (![A_97]: (k1_xboole_0=A_97 | ~v1_xboole_0(A_97))), inference(resolution, [status(thm)], [c_388, c_348])).
% 3.03/1.43  tff(c_863, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_854, c_399])).
% 3.03/1.43  tff(c_868, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_863])).
% 3.03/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.43  
% 3.03/1.43  Inference rules
% 3.03/1.43  ----------------------
% 3.03/1.43  #Ref     : 0
% 3.03/1.43  #Sup     : 178
% 3.03/1.43  #Fact    : 0
% 3.03/1.43  #Define  : 0
% 3.03/1.43  #Split   : 5
% 3.03/1.43  #Chain   : 0
% 3.03/1.43  #Close   : 0
% 3.03/1.43  
% 3.03/1.43  Ordering : KBO
% 3.03/1.43  
% 3.03/1.43  Simplification rules
% 3.03/1.43  ----------------------
% 3.03/1.43  #Subsume      : 21
% 3.03/1.43  #Demod        : 51
% 3.03/1.43  #Tautology    : 68
% 3.03/1.43  #SimpNegUnit  : 19
% 3.03/1.43  #BackRed      : 7
% 3.03/1.43  
% 3.03/1.43  #Partial instantiations: 0
% 3.03/1.43  #Strategies tried      : 1
% 3.03/1.43  
% 3.03/1.43  Timing (in seconds)
% 3.03/1.43  ----------------------
% 3.03/1.44  Preprocessing        : 0.32
% 3.03/1.44  Parsing              : 0.17
% 3.03/1.44  CNF conversion       : 0.02
% 3.03/1.44  Main loop            : 0.35
% 3.03/1.44  Inferencing          : 0.13
% 3.03/1.44  Reduction            : 0.11
% 3.03/1.44  Demodulation         : 0.07
% 3.03/1.44  BG Simplification    : 0.02
% 3.03/1.44  Subsumption          : 0.06
% 3.03/1.44  Abstraction          : 0.02
% 3.03/1.44  MUC search           : 0.00
% 3.03/1.44  Cooper               : 0.00
% 3.03/1.44  Total                : 0.70
% 3.03/1.44  Index Insertion      : 0.00
% 3.03/1.44  Index Deletion       : 0.00
% 3.03/1.44  Index Matching       : 0.00
% 3.03/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------

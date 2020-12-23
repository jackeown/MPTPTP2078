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
% DateTime   : Thu Dec  3 10:28:39 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   66 (  83 expanded)
%              Number of leaves         :   34 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :   81 ( 127 expanded)
%              Number of equality atoms :   21 (  25 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_62,axiom,(
    ! [A,B,C,D,E,F] :
      ( F = k3_enumset1(A,B,C,D,E)
    <=> ! [G] :
          ( r2_hidden(G,F)
        <=> ~ ( G != A
              & G != B
              & G != C
              & G != D
              & G != E ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

tff(f_75,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_4,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_62,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_66,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_130,plain,(
    ! [A_102,B_103] :
      ( k6_domain_1(A_102,B_103) = k1_tarski(B_103)
      | ~ m1_subset_1(B_103,A_102)
      | v1_xboole_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_133,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_130])).

tff(c_136,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_133])).

tff(c_64,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_137,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_64])).

tff(c_142,plain,(
    ! [A_104,B_105] :
      ( m1_subset_1(k6_domain_1(A_104,B_105),k1_zfmisc_1(A_104))
      | ~ m1_subset_1(B_105,A_104)
      | v1_xboole_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_151,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_142])).

tff(c_155,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_151])).

tff(c_156,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_155])).

tff(c_393,plain,(
    ! [B_157,A_158] :
      ( ~ v1_subset_1(B_157,A_158)
      | v1_xboole_0(B_157)
      | ~ m1_subset_1(B_157,k1_zfmisc_1(A_158))
      | ~ v1_zfmisc_1(A_158)
      | v1_xboole_0(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_396,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4'))
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_156,c_393])).

tff(c_402,plain,
    ( v1_xboole_0(k1_tarski('#skF_4'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_137,c_396])).

tff(c_403,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_402])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_408,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_403,c_2])).

tff(c_6,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_4,B_5] : k1_enumset1(A_4,A_4,B_5) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8] : k2_enumset1(A_6,A_6,B_7,C_8) = k1_enumset1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_157,plain,(
    ! [A_106,B_107,C_108,D_109] : k3_enumset1(A_106,A_106,B_107,C_108,D_109) = k2_enumset1(A_106,B_107,C_108,D_109) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [E_22,G_26,A_18,C_20,B_19] : r2_hidden(G_26,k3_enumset1(A_18,B_19,C_20,G_26,E_22)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_206,plain,(
    ! [C_110,A_111,B_112,D_113] : r2_hidden(C_110,k2_enumset1(A_111,B_112,C_110,D_113)) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_20])).

tff(c_214,plain,(
    ! [B_114,A_115,C_116] : r2_hidden(B_114,k1_enumset1(A_115,B_114,C_116)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_206])).

tff(c_380,plain,(
    ! [A_154,B_155] : r2_hidden(A_154,k2_tarski(A_154,B_155)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_214])).

tff(c_386,plain,(
    ! [A_3] : r2_hidden(A_3,k1_tarski(A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_380])).

tff(c_416,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_386])).

tff(c_54,plain,(
    ! [B_31,A_30] :
      ( ~ r1_tarski(B_31,A_30)
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_427,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_416,c_54])).

tff(c_431,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_427])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:37:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.41  
% 2.56/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.41  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 2.56/1.41  
% 2.56/1.41  %Foreground sorts:
% 2.56/1.41  
% 2.56/1.41  
% 2.56/1.41  %Background operators:
% 2.56/1.41  
% 2.56/1.41  
% 2.56/1.41  %Foreground operators:
% 2.56/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 2.56/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 2.56/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.56/1.41  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.56/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.56/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.56/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.56/1.41  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.56/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.56/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.56/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.56/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.56/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.56/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.56/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.56/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.56/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.41  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.56/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.56/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.56/1.41  
% 2.56/1.42  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.56/1.42  tff(f_115, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.56/1.42  tff(f_89, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.56/1.42  tff(f_82, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.56/1.42  tff(f_103, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.56/1.42  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.56/1.42  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.56/1.42  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.56/1.42  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.56/1.42  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.56/1.42  tff(f_62, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_enumset1)).
% 2.56/1.42  tff(f_75, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.56/1.42  tff(c_4, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.56/1.42  tff(c_68, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.56/1.42  tff(c_62, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.56/1.42  tff(c_66, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.56/1.42  tff(c_130, plain, (![A_102, B_103]: (k6_domain_1(A_102, B_103)=k1_tarski(B_103) | ~m1_subset_1(B_103, A_102) | v1_xboole_0(A_102))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.56/1.42  tff(c_133, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_66, c_130])).
% 2.56/1.42  tff(c_136, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_68, c_133])).
% 2.56/1.42  tff(c_64, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.56/1.42  tff(c_137, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_64])).
% 2.56/1.42  tff(c_142, plain, (![A_104, B_105]: (m1_subset_1(k6_domain_1(A_104, B_105), k1_zfmisc_1(A_104)) | ~m1_subset_1(B_105, A_104) | v1_xboole_0(A_104))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.56/1.42  tff(c_151, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_136, c_142])).
% 2.56/1.42  tff(c_155, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_151])).
% 2.56/1.42  tff(c_156, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_68, c_155])).
% 2.56/1.42  tff(c_393, plain, (![B_157, A_158]: (~v1_subset_1(B_157, A_158) | v1_xboole_0(B_157) | ~m1_subset_1(B_157, k1_zfmisc_1(A_158)) | ~v1_zfmisc_1(A_158) | v1_xboole_0(A_158))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.56/1.42  tff(c_396, plain, (~v1_subset_1(k1_tarski('#skF_4'), '#skF_3') | v1_xboole_0(k1_tarski('#skF_4')) | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_156, c_393])).
% 2.56/1.42  tff(c_402, plain, (v1_xboole_0(k1_tarski('#skF_4')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_137, c_396])).
% 2.56/1.42  tff(c_403, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_68, c_402])).
% 2.56/1.42  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.56/1.42  tff(c_408, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_403, c_2])).
% 2.56/1.42  tff(c_6, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.56/1.42  tff(c_8, plain, (![A_4, B_5]: (k1_enumset1(A_4, A_4, B_5)=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.56/1.42  tff(c_10, plain, (![A_6, B_7, C_8]: (k2_enumset1(A_6, A_6, B_7, C_8)=k1_enumset1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.56/1.42  tff(c_157, plain, (![A_106, B_107, C_108, D_109]: (k3_enumset1(A_106, A_106, B_107, C_108, D_109)=k2_enumset1(A_106, B_107, C_108, D_109))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.56/1.42  tff(c_20, plain, (![E_22, G_26, A_18, C_20, B_19]: (r2_hidden(G_26, k3_enumset1(A_18, B_19, C_20, G_26, E_22)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.56/1.42  tff(c_206, plain, (![C_110, A_111, B_112, D_113]: (r2_hidden(C_110, k2_enumset1(A_111, B_112, C_110, D_113)))), inference(superposition, [status(thm), theory('equality')], [c_157, c_20])).
% 2.56/1.42  tff(c_214, plain, (![B_114, A_115, C_116]: (r2_hidden(B_114, k1_enumset1(A_115, B_114, C_116)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_206])).
% 2.56/1.42  tff(c_380, plain, (![A_154, B_155]: (r2_hidden(A_154, k2_tarski(A_154, B_155)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_214])).
% 2.56/1.42  tff(c_386, plain, (![A_3]: (r2_hidden(A_3, k1_tarski(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_380])).
% 2.56/1.42  tff(c_416, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_408, c_386])).
% 2.56/1.42  tff(c_54, plain, (![B_31, A_30]: (~r1_tarski(B_31, A_30) | ~r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.56/1.42  tff(c_427, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_416, c_54])).
% 2.56/1.42  tff(c_431, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_427])).
% 2.56/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.42  
% 2.56/1.42  Inference rules
% 2.56/1.42  ----------------------
% 2.56/1.42  #Ref     : 0
% 2.56/1.42  #Sup     : 81
% 2.56/1.42  #Fact    : 0
% 2.56/1.42  #Define  : 0
% 2.56/1.42  #Split   : 1
% 2.56/1.42  #Chain   : 0
% 2.56/1.42  #Close   : 0
% 2.56/1.42  
% 2.56/1.42  Ordering : KBO
% 2.56/1.42  
% 2.56/1.42  Simplification rules
% 2.56/1.42  ----------------------
% 2.56/1.42  #Subsume      : 5
% 2.56/1.42  #Demod        : 27
% 2.56/1.42  #Tautology    : 27
% 2.56/1.42  #SimpNegUnit  : 5
% 2.56/1.42  #BackRed      : 11
% 2.56/1.42  
% 2.56/1.42  #Partial instantiations: 0
% 2.56/1.42  #Strategies tried      : 1
% 2.56/1.42  
% 2.56/1.42  Timing (in seconds)
% 2.56/1.42  ----------------------
% 2.56/1.43  Preprocessing        : 0.36
% 2.56/1.43  Parsing              : 0.18
% 2.56/1.43  CNF conversion       : 0.03
% 2.56/1.43  Main loop            : 0.26
% 2.56/1.43  Inferencing          : 0.09
% 2.56/1.43  Reduction            : 0.08
% 2.56/1.43  Demodulation         : 0.05
% 2.56/1.43  BG Simplification    : 0.02
% 2.56/1.43  Subsumption          : 0.06
% 2.56/1.43  Abstraction          : 0.02
% 2.56/1.43  MUC search           : 0.00
% 2.56/1.43  Cooper               : 0.00
% 2.56/1.43  Total                : 0.65
% 2.56/1.43  Index Insertion      : 0.00
% 2.56/1.43  Index Deletion       : 0.00
% 2.56/1.43  Index Matching       : 0.00
% 2.56/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------

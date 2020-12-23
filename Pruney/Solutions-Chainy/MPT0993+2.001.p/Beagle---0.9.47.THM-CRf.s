%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:42 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   59 (  80 expanded)
%              Number of leaves         :   29 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   86 ( 144 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_46,axiom,(
    ! [A,B] : r1_tarski(k1_relat_1(k2_zfmisc_1(A,B)),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_254,plain,(
    ! [A_76,B_77,D_78] :
      ( r2_relset_1(A_76,B_77,D_78,D_78)
      | ~ m1_subset_1(D_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_261,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_254])).

tff(c_10,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_49,plain,(
    ! [B_37,A_38] :
      ( v1_relat_1(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_55,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_49])).

tff(c_59,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_55])).

tff(c_39,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | ~ m1_subset_1(A_33,k1_zfmisc_1(B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_43,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_39])).

tff(c_314,plain,(
    ! [A_93,B_94] :
      ( r1_tarski(k1_relat_1(A_93),k1_relat_1(B_94))
      | ~ r1_tarski(A_93,B_94)
      | ~ v1_relat_1(B_94)
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [A_11,B_12] : r1_tarski(k1_relat_1(k2_zfmisc_1(A_11,B_12)),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_100,plain,(
    ! [A_52,C_53,B_54] :
      ( r1_tarski(A_52,C_53)
      | ~ r1_tarski(B_54,C_53)
      | ~ r1_tarski(A_52,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_108,plain,(
    ! [A_52,A_11,B_12] :
      ( r1_tarski(A_52,A_11)
      | ~ r1_tarski(A_52,k1_relat_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(resolution,[status(thm)],[c_12,c_100])).

tff(c_322,plain,(
    ! [A_93,A_11,B_12] :
      ( r1_tarski(k1_relat_1(A_93),A_11)
      | ~ r1_tarski(A_93,k2_zfmisc_1(A_11,B_12))
      | ~ v1_relat_1(k2_zfmisc_1(A_11,B_12))
      | ~ v1_relat_1(A_93) ) ),
    inference(resolution,[status(thm)],[c_314,c_108])).

tff(c_339,plain,(
    ! [A_95,A_96,B_97] :
      ( r1_tarski(k1_relat_1(A_95),A_96)
      | ~ r1_tarski(A_95,k2_zfmisc_1(A_96,B_97))
      | ~ v1_relat_1(A_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_322])).

tff(c_346,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_43,c_339])).

tff(c_356,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_346])).

tff(c_30,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_109,plain,(
    ! [A_52] :
      ( r1_tarski(A_52,'#skF_3')
      | ~ r1_tarski(A_52,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_100])).

tff(c_139,plain,(
    ! [B_59,A_60] :
      ( k7_relat_1(B_59,A_60) = B_59
      | ~ r1_tarski(k1_relat_1(B_59),A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_152,plain,(
    ! [B_59] :
      ( k7_relat_1(B_59,'#skF_3') = B_59
      | ~ v1_relat_1(B_59)
      | ~ r1_tarski(k1_relat_1(B_59),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_109,c_139])).

tff(c_364,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_356,c_152])).

tff(c_378,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_364])).

tff(c_36,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_576,plain,(
    ! [A_110,B_111,C_112,D_113] :
      ( k2_partfun1(A_110,B_111,C_112,D_113) = k7_relat_1(C_112,D_113)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | ~ v1_funct_1(C_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_581,plain,(
    ! [D_113] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_113) = k7_relat_1('#skF_4',D_113)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_576])).

tff(c_585,plain,(
    ! [D_113] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_113) = k7_relat_1('#skF_4',D_113) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_581])).

tff(c_28,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_586,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_585,c_28])).

tff(c_589,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_378,c_586])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:56:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.36  
% 2.65/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.36  %$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.65/1.36  
% 2.65/1.36  %Foreground sorts:
% 2.65/1.36  
% 2.65/1.36  
% 2.65/1.36  %Background operators:
% 2.65/1.36  
% 2.65/1.36  
% 2.65/1.36  %Foreground operators:
% 2.65/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.65/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.36  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.65/1.36  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.65/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.65/1.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.65/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.65/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.65/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.65/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.65/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.65/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.65/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.65/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.36  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.65/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.65/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.65/1.36  
% 2.76/1.38  tff(f_92, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_2)).
% 2.76/1.38  tff(f_75, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.76/1.38  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.76/1.38  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.76/1.38  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.76/1.38  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 2.76/1.38  tff(f_46, axiom, (![A, B]: r1_tarski(k1_relat_1(k2_zfmisc_1(A, B)), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_relat_1)).
% 2.76/1.38  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.76/1.38  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.76/1.38  tff(f_81, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.76/1.38  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.76/1.38  tff(c_254, plain, (![A_76, B_77, D_78]: (r2_relset_1(A_76, B_77, D_78, D_78) | ~m1_subset_1(D_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.76/1.38  tff(c_261, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_254])).
% 2.76/1.38  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.76/1.38  tff(c_49, plain, (![B_37, A_38]: (v1_relat_1(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.76/1.38  tff(c_55, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_49])).
% 2.76/1.38  tff(c_59, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_55])).
% 2.76/1.38  tff(c_39, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | ~m1_subset_1(A_33, k1_zfmisc_1(B_34)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.76/1.38  tff(c_43, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_39])).
% 2.76/1.38  tff(c_314, plain, (![A_93, B_94]: (r1_tarski(k1_relat_1(A_93), k1_relat_1(B_94)) | ~r1_tarski(A_93, B_94) | ~v1_relat_1(B_94) | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.76/1.38  tff(c_12, plain, (![A_11, B_12]: (r1_tarski(k1_relat_1(k2_zfmisc_1(A_11, B_12)), A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.76/1.38  tff(c_100, plain, (![A_52, C_53, B_54]: (r1_tarski(A_52, C_53) | ~r1_tarski(B_54, C_53) | ~r1_tarski(A_52, B_54))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.76/1.38  tff(c_108, plain, (![A_52, A_11, B_12]: (r1_tarski(A_52, A_11) | ~r1_tarski(A_52, k1_relat_1(k2_zfmisc_1(A_11, B_12))))), inference(resolution, [status(thm)], [c_12, c_100])).
% 2.76/1.38  tff(c_322, plain, (![A_93, A_11, B_12]: (r1_tarski(k1_relat_1(A_93), A_11) | ~r1_tarski(A_93, k2_zfmisc_1(A_11, B_12)) | ~v1_relat_1(k2_zfmisc_1(A_11, B_12)) | ~v1_relat_1(A_93))), inference(resolution, [status(thm)], [c_314, c_108])).
% 2.76/1.38  tff(c_339, plain, (![A_95, A_96, B_97]: (r1_tarski(k1_relat_1(A_95), A_96) | ~r1_tarski(A_95, k2_zfmisc_1(A_96, B_97)) | ~v1_relat_1(A_95))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_322])).
% 2.76/1.38  tff(c_346, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_43, c_339])).
% 2.76/1.38  tff(c_356, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_346])).
% 2.76/1.38  tff(c_30, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.76/1.38  tff(c_109, plain, (![A_52]: (r1_tarski(A_52, '#skF_3') | ~r1_tarski(A_52, '#skF_1'))), inference(resolution, [status(thm)], [c_30, c_100])).
% 2.76/1.38  tff(c_139, plain, (![B_59, A_60]: (k7_relat_1(B_59, A_60)=B_59 | ~r1_tarski(k1_relat_1(B_59), A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.76/1.38  tff(c_152, plain, (![B_59]: (k7_relat_1(B_59, '#skF_3')=B_59 | ~v1_relat_1(B_59) | ~r1_tarski(k1_relat_1(B_59), '#skF_1'))), inference(resolution, [status(thm)], [c_109, c_139])).
% 2.76/1.38  tff(c_364, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_356, c_152])).
% 2.76/1.38  tff(c_378, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_59, c_364])).
% 2.76/1.38  tff(c_36, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.76/1.38  tff(c_576, plain, (![A_110, B_111, C_112, D_113]: (k2_partfun1(A_110, B_111, C_112, D_113)=k7_relat_1(C_112, D_113) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | ~v1_funct_1(C_112))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.76/1.38  tff(c_581, plain, (![D_113]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_113)=k7_relat_1('#skF_4', D_113) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_576])).
% 2.76/1.38  tff(c_585, plain, (![D_113]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_113)=k7_relat_1('#skF_4', D_113))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_581])).
% 2.76/1.38  tff(c_28, plain, (~r2_relset_1('#skF_1', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.76/1.38  tff(c_586, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_585, c_28])).
% 2.76/1.38  tff(c_589, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_261, c_378, c_586])).
% 2.76/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.38  
% 2.76/1.38  Inference rules
% 2.76/1.38  ----------------------
% 2.76/1.38  #Ref     : 0
% 2.76/1.38  #Sup     : 118
% 2.76/1.38  #Fact    : 0
% 2.76/1.38  #Define  : 0
% 2.76/1.38  #Split   : 6
% 2.76/1.38  #Chain   : 0
% 2.76/1.38  #Close   : 0
% 2.76/1.38  
% 2.76/1.38  Ordering : KBO
% 2.76/1.38  
% 2.76/1.38  Simplification rules
% 2.76/1.38  ----------------------
% 2.76/1.38  #Subsume      : 11
% 2.76/1.38  #Demod        : 35
% 2.76/1.38  #Tautology    : 15
% 2.76/1.38  #SimpNegUnit  : 0
% 2.76/1.38  #BackRed      : 1
% 2.76/1.38  
% 2.76/1.38  #Partial instantiations: 0
% 2.76/1.38  #Strategies tried      : 1
% 2.76/1.38  
% 2.76/1.38  Timing (in seconds)
% 2.76/1.38  ----------------------
% 2.76/1.38  Preprocessing        : 0.30
% 2.76/1.38  Parsing              : 0.16
% 2.76/1.38  CNF conversion       : 0.02
% 2.76/1.38  Main loop            : 0.32
% 2.76/1.38  Inferencing          : 0.12
% 2.76/1.38  Reduction            : 0.10
% 2.76/1.38  Demodulation         : 0.07
% 2.76/1.38  BG Simplification    : 0.02
% 2.76/1.38  Subsumption          : 0.06
% 2.76/1.38  Abstraction          : 0.02
% 2.76/1.38  MUC search           : 0.00
% 2.76/1.38  Cooper               : 0.00
% 2.76/1.38  Total                : 0.65
% 2.76/1.38  Index Insertion      : 0.00
% 2.76/1.38  Index Deletion       : 0.00
% 2.76/1.38  Index Matching       : 0.00
% 2.76/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------

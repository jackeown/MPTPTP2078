%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:17 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   62 (  93 expanded)
%              Number of leaves         :   31 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :  103 ( 234 expanded)
%              Number of equality atoms :   22 (  38 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v1_funct_1(B)
              & v1_funct_2(B,A,A)
              & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v5_relat_1(C,A)
                  & v1_funct_1(C) )
               => k1_relat_1(k5_relat_1(C,B)) = k1_relat_1(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t200_funct_2)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k1_relat_1(A) = k1_relat_1(B)
               => k1_relat_1(k5_relat_1(C,A)) = k1_relat_1(k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_relat_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_6,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_11] : k1_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_178,plain,(
    ! [B_63,A_64] :
      ( k5_relat_1(B_63,k6_relat_1(A_64)) = B_63
      | ~ r1_tarski(k2_relat_1(B_63),A_64)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_185,plain,(
    ! [B_2,A_1] :
      ( k5_relat_1(B_2,k6_relat_1(A_1)) = B_2
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_178])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_64,plain,(
    ! [C_33,A_34,B_35] :
      ( v1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_68,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_64])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_91,plain,(
    ! [C_44,A_45,B_46] :
      ( v4_relat_1(C_44,A_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_95,plain,(
    v4_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_91])).

tff(c_108,plain,(
    ! [B_52,A_53] :
      ( k1_relat_1(B_52) = A_53
      | ~ v1_partfun1(B_52,A_53)
      | ~ v4_relat_1(B_52,A_53)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_111,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_95,c_108])).

tff(c_114,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_111])).

tff(c_115,plain,(
    ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_42,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_40,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_157,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_partfun1(C_60,A_61)
      | ~ v1_funct_2(C_60,A_61,B_62)
      | ~ v1_funct_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62)))
      | v1_xboole_0(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_160,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_157])).

tff(c_163,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_160])).

tff(c_165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_115,c_163])).

tff(c_166,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_227,plain,(
    ! [C_72,B_73,A_74] :
      ( k1_relat_1(k5_relat_1(C_72,B_73)) = k1_relat_1(k5_relat_1(C_72,A_74))
      | k1_relat_1(B_73) != k1_relat_1(A_74)
      | ~ v1_relat_1(C_72)
      | ~ v1_relat_1(B_73)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30,plain,(
    k1_relat_1(k5_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_248,plain,(
    ! [B_73] :
      ( k1_relat_1(k5_relat_1('#skF_3',B_73)) != k1_relat_1('#skF_3')
      | k1_relat_1(B_73) != k1_relat_1('#skF_2')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(B_73)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_30])).

tff(c_288,plain,(
    ! [B_75] :
      ( k1_relat_1(k5_relat_1('#skF_3',B_75)) != k1_relat_1('#skF_3')
      | k1_relat_1(B_75) != '#skF_1'
      | ~ v1_relat_1(B_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_36,c_166,c_248])).

tff(c_300,plain,(
    ! [A_1] :
      ( k1_relat_1(k6_relat_1(A_1)) != '#skF_1'
      | ~ v1_relat_1(k6_relat_1(A_1))
      | ~ v5_relat_1('#skF_3',A_1)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_288])).

tff(c_308,plain,(
    ~ v5_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6,c_10,c_300])).

tff(c_34,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_308,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.50  
% 2.50/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.51  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.50/1.51  
% 2.50/1.51  %Foreground sorts:
% 2.50/1.51  
% 2.50/1.51  
% 2.50/1.51  %Background operators:
% 2.50/1.51  
% 2.50/1.51  
% 2.50/1.51  %Foreground operators:
% 2.50/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.50/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.51  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.50/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.50/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.50/1.51  tff('#skF_2', type, '#skF_2': $i).
% 2.50/1.51  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.50/1.51  tff('#skF_3', type, '#skF_3': $i).
% 2.50/1.51  tff('#skF_1', type, '#skF_1': $i).
% 2.50/1.51  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.50/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.50/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.50/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.50/1.51  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.50/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.51  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.50/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.50/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.50/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.50/1.51  
% 2.50/1.52  tff(f_107, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (k1_relat_1(k5_relat_1(C, B)) = k1_relat_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t200_funct_2)).
% 2.50/1.52  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.50/1.52  tff(f_49, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.50/1.52  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.50/1.52  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 2.50/1.52  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.50/1.52  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.50/1.52  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 2.50/1.52  tff(f_79, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.50/1.52  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k1_relat_1(A) = k1_relat_1(B)) => (k1_relat_1(k5_relat_1(C, A)) = k1_relat_1(k5_relat_1(C, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t198_relat_1)).
% 2.50/1.52  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.50/1.52  tff(c_6, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.50/1.52  tff(c_10, plain, (![A_11]: (k1_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.50/1.52  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.50/1.52  tff(c_178, plain, (![B_63, A_64]: (k5_relat_1(B_63, k6_relat_1(A_64))=B_63 | ~r1_tarski(k2_relat_1(B_63), A_64) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.50/1.52  tff(c_185, plain, (![B_2, A_1]: (k5_relat_1(B_2, k6_relat_1(A_1))=B_2 | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_4, c_178])).
% 2.50/1.52  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.50/1.52  tff(c_64, plain, (![C_33, A_34, B_35]: (v1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.50/1.52  tff(c_68, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_38, c_64])).
% 2.50/1.52  tff(c_44, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.50/1.52  tff(c_91, plain, (![C_44, A_45, B_46]: (v4_relat_1(C_44, A_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.50/1.52  tff(c_95, plain, (v4_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_91])).
% 2.50/1.52  tff(c_108, plain, (![B_52, A_53]: (k1_relat_1(B_52)=A_53 | ~v1_partfun1(B_52, A_53) | ~v4_relat_1(B_52, A_53) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.50/1.52  tff(c_111, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v1_partfun1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_95, c_108])).
% 2.50/1.52  tff(c_114, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v1_partfun1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_111])).
% 2.50/1.52  tff(c_115, plain, (~v1_partfun1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_114])).
% 2.50/1.52  tff(c_42, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.50/1.52  tff(c_40, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.50/1.52  tff(c_157, plain, (![C_60, A_61, B_62]: (v1_partfun1(C_60, A_61) | ~v1_funct_2(C_60, A_61, B_62) | ~v1_funct_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))) | v1_xboole_0(B_62))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.50/1.52  tff(c_160, plain, (v1_partfun1('#skF_2', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_157])).
% 2.50/1.52  tff(c_163, plain, (v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_160])).
% 2.50/1.52  tff(c_165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_115, c_163])).
% 2.50/1.52  tff(c_166, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_114])).
% 2.50/1.52  tff(c_227, plain, (![C_72, B_73, A_74]: (k1_relat_1(k5_relat_1(C_72, B_73))=k1_relat_1(k5_relat_1(C_72, A_74)) | k1_relat_1(B_73)!=k1_relat_1(A_74) | ~v1_relat_1(C_72) | ~v1_relat_1(B_73) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.50/1.52  tff(c_30, plain, (k1_relat_1(k5_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.50/1.52  tff(c_248, plain, (![B_73]: (k1_relat_1(k5_relat_1('#skF_3', B_73))!=k1_relat_1('#skF_3') | k1_relat_1(B_73)!=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1(B_73) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_227, c_30])).
% 2.50/1.52  tff(c_288, plain, (![B_75]: (k1_relat_1(k5_relat_1('#skF_3', B_75))!=k1_relat_1('#skF_3') | k1_relat_1(B_75)!='#skF_1' | ~v1_relat_1(B_75))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_36, c_166, c_248])).
% 2.50/1.52  tff(c_300, plain, (![A_1]: (k1_relat_1(k6_relat_1(A_1))!='#skF_1' | ~v1_relat_1(k6_relat_1(A_1)) | ~v5_relat_1('#skF_3', A_1) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_185, c_288])).
% 2.50/1.52  tff(c_308, plain, (~v5_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_6, c_10, c_300])).
% 2.50/1.52  tff(c_34, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.50/1.52  tff(c_310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_308, c_34])).
% 2.50/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.52  
% 2.50/1.52  Inference rules
% 2.50/1.52  ----------------------
% 2.50/1.52  #Ref     : 0
% 2.50/1.52  #Sup     : 53
% 2.50/1.52  #Fact    : 0
% 2.50/1.52  #Define  : 0
% 2.50/1.52  #Split   : 1
% 2.50/1.52  #Chain   : 0
% 2.50/1.52  #Close   : 0
% 2.50/1.52  
% 2.50/1.52  Ordering : KBO
% 2.50/1.52  
% 2.50/1.52  Simplification rules
% 2.50/1.52  ----------------------
% 2.50/1.52  #Subsume      : 1
% 2.50/1.52  #Demod        : 43
% 2.50/1.52  #Tautology    : 23
% 2.50/1.52  #SimpNegUnit  : 3
% 2.50/1.52  #BackRed      : 1
% 2.50/1.52  
% 2.50/1.52  #Partial instantiations: 0
% 2.50/1.52  #Strategies tried      : 1
% 2.50/1.52  
% 2.50/1.52  Timing (in seconds)
% 2.50/1.52  ----------------------
% 2.77/1.52  Preprocessing        : 0.38
% 2.77/1.52  Parsing              : 0.20
% 2.77/1.52  CNF conversion       : 0.02
% 2.77/1.52  Main loop            : 0.25
% 2.77/1.52  Inferencing          : 0.10
% 2.77/1.52  Reduction            : 0.08
% 2.77/1.52  Demodulation         : 0.06
% 2.77/1.52  BG Simplification    : 0.02
% 2.77/1.52  Subsumption          : 0.03
% 2.77/1.52  Abstraction          : 0.01
% 2.77/1.52  MUC search           : 0.00
% 2.77/1.52  Cooper               : 0.00
% 2.77/1.52  Total                : 0.66
% 2.77/1.52  Index Insertion      : 0.00
% 2.77/1.52  Index Deletion       : 0.00
% 2.77/1.53  Index Matching       : 0.00
% 2.77/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------

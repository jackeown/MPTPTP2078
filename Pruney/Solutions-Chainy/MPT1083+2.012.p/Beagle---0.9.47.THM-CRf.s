%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:18 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 102 expanded)
%              Number of leaves         :   32 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :  110 ( 253 expanded)
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

tff(f_114,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t200_funct_2)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k1_relat_1(A) = k1_relat_1(B)
               => k1_relat_1(k5_relat_1(C,A)) = k1_relat_1(k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_18,plain,(
    ! [A_18] : v1_relat_1(k6_relat_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_12,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_155,plain,(
    ! [B_63,A_64] :
      ( k5_relat_1(B_63,k6_relat_1(A_64)) = B_63
      | ~ r1_tarski(k2_relat_1(B_63),A_64)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_162,plain,(
    ! [B_5,A_4] :
      ( k5_relat_1(B_5,k6_relat_1(A_4)) = B_5
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_155])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_70,plain,(
    ! [B_38,A_39] :
      ( v1_relat_1(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_39))
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_73,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_42,c_70])).

tff(c_76,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_73])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_104,plain,(
    ! [C_51,A_52,B_53] :
      ( v4_relat_1(C_51,A_52)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_108,plain,(
    v4_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_104])).

tff(c_116,plain,(
    ! [B_56,A_57] :
      ( k1_relat_1(B_56) = A_57
      | ~ v1_partfun1(B_56,A_57)
      | ~ v4_relat_1(B_56,A_57)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_119,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_108,c_116])).

tff(c_122,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_119])).

tff(c_123,plain,(
    ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_46,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_44,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_134,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_partfun1(C_60,A_61)
      | ~ v1_funct_2(C_60,A_61,B_62)
      | ~ v1_funct_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62)))
      | v1_xboole_0(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_137,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_134])).

tff(c_140,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_137])).

tff(c_142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_123,c_140])).

tff(c_143,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_204,plain,(
    ! [C_72,B_73,A_74] :
      ( k1_relat_1(k5_relat_1(C_72,B_73)) = k1_relat_1(k5_relat_1(C_72,A_74))
      | k1_relat_1(B_73) != k1_relat_1(A_74)
      | ~ v1_relat_1(C_72)
      | ~ v1_relat_1(B_73)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_34,plain,(
    k1_relat_1(k5_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_225,plain,(
    ! [B_73] :
      ( k1_relat_1(k5_relat_1('#skF_3',B_73)) != k1_relat_1('#skF_3')
      | k1_relat_1(B_73) != k1_relat_1('#skF_2')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(B_73)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_34])).

tff(c_265,plain,(
    ! [B_75] :
      ( k1_relat_1(k5_relat_1('#skF_3',B_75)) != k1_relat_1('#skF_3')
      | k1_relat_1(B_75) != '#skF_1'
      | ~ v1_relat_1(B_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_40,c_143,c_225])).

tff(c_277,plain,(
    ! [A_4] :
      ( k1_relat_1(k6_relat_1(A_4)) != '#skF_1'
      | ~ v1_relat_1(k6_relat_1(A_4))
      | ~ v5_relat_1('#skF_3',A_4)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_265])).

tff(c_285,plain,(
    ~ v5_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_18,c_12,c_277])).

tff(c_38,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_287,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_285,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:18:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.38  
% 2.11/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.38  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.11/1.38  
% 2.11/1.38  %Foreground sorts:
% 2.11/1.38  
% 2.11/1.38  
% 2.11/1.38  %Background operators:
% 2.11/1.38  
% 2.11/1.38  
% 2.11/1.38  %Foreground operators:
% 2.11/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.11/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.38  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.11/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.11/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.11/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.38  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.11/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.11/1.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.11/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.11/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.11/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.11/1.38  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.47/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.47/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.47/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.47/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.47/1.38  
% 2.47/1.41  tff(f_114, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (k1_relat_1(k5_relat_1(C, B)) = k1_relat_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t200_funct_2)).
% 2.47/1.41  tff(f_66, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.47/1.41  tff(f_56, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.47/1.41  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.47/1.41  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 2.47/1.41  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.47/1.41  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.47/1.41  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.47/1.41  tff(f_94, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 2.47/1.41  tff(f_86, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.47/1.41  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k1_relat_1(A) = k1_relat_1(B)) => (k1_relat_1(k5_relat_1(C, A)) = k1_relat_1(k5_relat_1(C, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t198_relat_1)).
% 2.47/1.41  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.47/1.41  tff(c_18, plain, (![A_18]: (v1_relat_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.47/1.41  tff(c_12, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.47/1.41  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.47/1.41  tff(c_155, plain, (![B_63, A_64]: (k5_relat_1(B_63, k6_relat_1(A_64))=B_63 | ~r1_tarski(k2_relat_1(B_63), A_64) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.47/1.41  tff(c_162, plain, (![B_5, A_4]: (k5_relat_1(B_5, k6_relat_1(A_4))=B_5 | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_155])).
% 2.47/1.41  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.47/1.41  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.47/1.41  tff(c_70, plain, (![B_38, A_39]: (v1_relat_1(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_39)) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.47/1.41  tff(c_73, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_42, c_70])).
% 2.47/1.41  tff(c_76, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_73])).
% 2.47/1.41  tff(c_48, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.47/1.41  tff(c_104, plain, (![C_51, A_52, B_53]: (v4_relat_1(C_51, A_52) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.47/1.41  tff(c_108, plain, (v4_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_104])).
% 2.47/1.41  tff(c_116, plain, (![B_56, A_57]: (k1_relat_1(B_56)=A_57 | ~v1_partfun1(B_56, A_57) | ~v4_relat_1(B_56, A_57) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.47/1.41  tff(c_119, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v1_partfun1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_108, c_116])).
% 2.47/1.41  tff(c_122, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v1_partfun1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_119])).
% 2.47/1.41  tff(c_123, plain, (~v1_partfun1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_122])).
% 2.47/1.41  tff(c_46, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.47/1.41  tff(c_44, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.47/1.41  tff(c_134, plain, (![C_60, A_61, B_62]: (v1_partfun1(C_60, A_61) | ~v1_funct_2(C_60, A_61, B_62) | ~v1_funct_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))) | v1_xboole_0(B_62))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.47/1.41  tff(c_137, plain, (v1_partfun1('#skF_2', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_134])).
% 2.47/1.41  tff(c_140, plain, (v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_137])).
% 2.47/1.41  tff(c_142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_123, c_140])).
% 2.47/1.41  tff(c_143, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_122])).
% 2.47/1.41  tff(c_204, plain, (![C_72, B_73, A_74]: (k1_relat_1(k5_relat_1(C_72, B_73))=k1_relat_1(k5_relat_1(C_72, A_74)) | k1_relat_1(B_73)!=k1_relat_1(A_74) | ~v1_relat_1(C_72) | ~v1_relat_1(B_73) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.47/1.41  tff(c_34, plain, (k1_relat_1(k5_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.47/1.41  tff(c_225, plain, (![B_73]: (k1_relat_1(k5_relat_1('#skF_3', B_73))!=k1_relat_1('#skF_3') | k1_relat_1(B_73)!=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1(B_73) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_204, c_34])).
% 2.47/1.41  tff(c_265, plain, (![B_75]: (k1_relat_1(k5_relat_1('#skF_3', B_75))!=k1_relat_1('#skF_3') | k1_relat_1(B_75)!='#skF_1' | ~v1_relat_1(B_75))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_40, c_143, c_225])).
% 2.47/1.41  tff(c_277, plain, (![A_4]: (k1_relat_1(k6_relat_1(A_4))!='#skF_1' | ~v1_relat_1(k6_relat_1(A_4)) | ~v5_relat_1('#skF_3', A_4) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_162, c_265])).
% 2.47/1.41  tff(c_285, plain, (~v5_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_18, c_12, c_277])).
% 2.47/1.41  tff(c_38, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.47/1.41  tff(c_287, plain, $false, inference(negUnitSimplification, [status(thm)], [c_285, c_38])).
% 2.47/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.41  
% 2.47/1.41  Inference rules
% 2.47/1.41  ----------------------
% 2.47/1.41  #Ref     : 0
% 2.47/1.41  #Sup     : 47
% 2.47/1.41  #Fact    : 0
% 2.47/1.41  #Define  : 0
% 2.47/1.41  #Split   : 1
% 2.47/1.41  #Chain   : 0
% 2.47/1.41  #Close   : 0
% 2.47/1.41  
% 2.47/1.41  Ordering : KBO
% 2.47/1.41  
% 2.47/1.41  Simplification rules
% 2.47/1.41  ----------------------
% 2.47/1.41  #Subsume      : 1
% 2.47/1.41  #Demod        : 42
% 2.47/1.41  #Tautology    : 17
% 2.47/1.41  #SimpNegUnit  : 3
% 2.47/1.41  #BackRed      : 1
% 2.47/1.41  
% 2.47/1.41  #Partial instantiations: 0
% 2.47/1.41  #Strategies tried      : 1
% 2.47/1.41  
% 2.47/1.41  Timing (in seconds)
% 2.47/1.41  ----------------------
% 2.53/1.41  Preprocessing        : 0.33
% 2.53/1.41  Parsing              : 0.19
% 2.53/1.42  CNF conversion       : 0.02
% 2.53/1.42  Main loop            : 0.25
% 2.53/1.42  Inferencing          : 0.09
% 2.53/1.42  Reduction            : 0.08
% 2.53/1.42  Demodulation         : 0.06
% 2.53/1.42  BG Simplification    : 0.02
% 2.53/1.42  Subsumption          : 0.04
% 2.53/1.42  Abstraction          : 0.01
% 2.53/1.42  MUC search           : 0.00
% 2.53/1.42  Cooper               : 0.00
% 2.53/1.42  Total                : 0.62
% 2.53/1.42  Index Insertion      : 0.00
% 2.53/1.42  Index Deletion       : 0.00
% 2.53/1.42  Index Matching       : 0.00
% 2.53/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------

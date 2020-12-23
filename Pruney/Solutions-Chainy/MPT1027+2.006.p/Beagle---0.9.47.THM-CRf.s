%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:42 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 100 expanded)
%              Number of leaves         :   29 (  46 expanded)
%              Depth                    :    6
%              Number of atoms          :  100 ( 221 expanded)
%              Number of equality atoms :   18 (  34 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_40,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_34,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_42,plain,(
    ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_34])).

tff(c_132,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_partfun1(C_56,A_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58)))
      | ~ v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_136,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_132])).

tff(c_137,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( v1_xboole_0(k2_zfmisc_1(A_5,B_6))
      | ~ v1_xboole_0(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_56,plain,(
    ! [B_31,A_32] :
      ( v1_xboole_0(B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_32))
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_60,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_56])).

tff(c_67,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_71,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_67])).

tff(c_36,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_110,plain,(
    ! [B_53,C_54,A_55] :
      ( k1_xboole_0 = B_53
      | v1_funct_2(C_54,A_55,B_53)
      | k1_relset_1(A_55,B_53,C_54) != A_55
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_113,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2')
    | k1_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_38,c_110])).

tff(c_116,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_113])).

tff(c_117,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_116])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : r1_xboole_0(A_2,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_51,plain,(
    ! [B_29,A_30] :
      ( ~ r1_xboole_0(B_29,A_30)
      | ~ r1_tarski(B_29,A_30)
      | v1_xboole_0(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_61,plain,(
    ! [A_33] :
      ( ~ r1_tarski(A_33,k1_xboole_0)
      | v1_xboole_0(A_33) ) ),
    inference(resolution,[status(thm)],[c_4,c_51])).

tff(c_66,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_61])).

tff(c_124,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_66])).

tff(c_129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_124])).

tff(c_130,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_138,plain,(
    ! [A_59,B_60,C_61] :
      ( k1_relset_1(A_59,B_60,C_61) = k1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_141,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_138])).

tff(c_143,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_141])).

tff(c_12,plain,(
    ! [A_10] :
      ( v1_xboole_0(k1_relat_1(A_10))
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_147,plain,
    ( v1_xboole_0('#skF_1')
    | ~ v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_12])).

tff(c_151,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_147])).

tff(c_153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_151])).

tff(c_154,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_175,plain,(
    ! [C_72,A_73,B_74] :
      ( v1_funct_2(C_72,A_73,B_74)
      | ~ v1_partfun1(C_72,A_73)
      | ~ v1_funct_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_178,plain,
    ( v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_175])).

tff(c_181,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_154,c_178])).

tff(c_183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_181])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:06:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.30  
% 2.03/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.30  %$ v1_funct_2 > v1_partfun1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.03/1.30  
% 2.03/1.30  %Foreground sorts:
% 2.03/1.30  
% 2.03/1.30  
% 2.03/1.30  %Background operators:
% 2.03/1.30  
% 2.03/1.30  
% 2.03/1.30  %Foreground operators:
% 2.03/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.03/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.03/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.03/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.03/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.03/1.30  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.03/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.03/1.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.03/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.03/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.03/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.03/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.03/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.03/1.30  
% 2.30/1.32  tff(f_104, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_funct_2)).
% 2.30/1.32  tff(f_73, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 2.30/1.32  tff(f_41, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 2.30/1.32  tff(f_48, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.30/1.32  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.30/1.32  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.30/1.32  tff(f_29, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.30/1.32  tff(f_37, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.30/1.32  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.30/1.32  tff(f_52, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 2.30/1.32  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 2.30/1.32  tff(c_40, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.30/1.32  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.30/1.32  tff(c_34, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.30/1.32  tff(c_42, plain, (~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_34])).
% 2.30/1.32  tff(c_132, plain, (![C_56, A_57, B_58]: (v1_partfun1(C_56, A_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))) | ~v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.30/1.32  tff(c_136, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_132])).
% 2.30/1.32  tff(c_137, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_136])).
% 2.30/1.32  tff(c_8, plain, (![A_5, B_6]: (v1_xboole_0(k2_zfmisc_1(A_5, B_6)) | ~v1_xboole_0(B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.30/1.32  tff(c_56, plain, (![B_31, A_32]: (v1_xboole_0(B_31) | ~m1_subset_1(B_31, k1_zfmisc_1(A_32)) | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.30/1.32  tff(c_60, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_56])).
% 2.30/1.32  tff(c_67, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_60])).
% 2.30/1.32  tff(c_71, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_8, c_67])).
% 2.30/1.32  tff(c_36, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.30/1.32  tff(c_110, plain, (![B_53, C_54, A_55]: (k1_xboole_0=B_53 | v1_funct_2(C_54, A_55, B_53) | k1_relset_1(A_55, B_53, C_54)!=A_55 | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_53))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.30/1.32  tff(c_113, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_38, c_110])).
% 2.30/1.32  tff(c_116, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_113])).
% 2.30/1.32  tff(c_117, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_42, c_116])).
% 2.30/1.32  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.30/1.32  tff(c_4, plain, (![A_2]: (r1_xboole_0(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.30/1.32  tff(c_51, plain, (![B_29, A_30]: (~r1_xboole_0(B_29, A_30) | ~r1_tarski(B_29, A_30) | v1_xboole_0(B_29))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.30/1.32  tff(c_61, plain, (![A_33]: (~r1_tarski(A_33, k1_xboole_0) | v1_xboole_0(A_33))), inference(resolution, [status(thm)], [c_4, c_51])).
% 2.30/1.32  tff(c_66, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_61])).
% 2.30/1.32  tff(c_124, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_117, c_66])).
% 2.30/1.32  tff(c_129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_124])).
% 2.30/1.32  tff(c_130, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_60])).
% 2.30/1.32  tff(c_138, plain, (![A_59, B_60, C_61]: (k1_relset_1(A_59, B_60, C_61)=k1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.30/1.32  tff(c_141, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_138])).
% 2.30/1.32  tff(c_143, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_141])).
% 2.30/1.32  tff(c_12, plain, (![A_10]: (v1_xboole_0(k1_relat_1(A_10)) | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.30/1.32  tff(c_147, plain, (v1_xboole_0('#skF_1') | ~v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_143, c_12])).
% 2.30/1.32  tff(c_151, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_147])).
% 2.30/1.32  tff(c_153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137, c_151])).
% 2.30/1.32  tff(c_154, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_136])).
% 2.30/1.32  tff(c_175, plain, (![C_72, A_73, B_74]: (v1_funct_2(C_72, A_73, B_74) | ~v1_partfun1(C_72, A_73) | ~v1_funct_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.30/1.32  tff(c_178, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_175])).
% 2.30/1.32  tff(c_181, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_154, c_178])).
% 2.30/1.32  tff(c_183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_181])).
% 2.30/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.32  
% 2.30/1.32  Inference rules
% 2.30/1.32  ----------------------
% 2.30/1.32  #Ref     : 0
% 2.30/1.32  #Sup     : 24
% 2.30/1.32  #Fact    : 0
% 2.30/1.32  #Define  : 0
% 2.30/1.32  #Split   : 3
% 2.30/1.32  #Chain   : 0
% 2.30/1.32  #Close   : 0
% 2.30/1.32  
% 2.30/1.32  Ordering : KBO
% 2.30/1.32  
% 2.30/1.32  Simplification rules
% 2.30/1.32  ----------------------
% 2.30/1.32  #Subsume      : 1
% 2.30/1.32  #Demod        : 36
% 2.30/1.32  #Tautology    : 9
% 2.30/1.32  #SimpNegUnit  : 6
% 2.30/1.32  #BackRed      : 10
% 2.30/1.32  
% 2.30/1.32  #Partial instantiations: 0
% 2.30/1.32  #Strategies tried      : 1
% 2.30/1.32  
% 2.30/1.32  Timing (in seconds)
% 2.30/1.32  ----------------------
% 2.30/1.32  Preprocessing        : 0.34
% 2.30/1.32  Parsing              : 0.18
% 2.30/1.32  CNF conversion       : 0.02
% 2.30/1.32  Main loop            : 0.17
% 2.30/1.32  Inferencing          : 0.06
% 2.30/1.32  Reduction            : 0.05
% 2.30/1.32  Demodulation         : 0.04
% 2.30/1.32  BG Simplification    : 0.01
% 2.30/1.32  Subsumption          : 0.03
% 2.30/1.32  Abstraction          : 0.01
% 2.30/1.32  MUC search           : 0.00
% 2.30/1.32  Cooper               : 0.00
% 2.30/1.32  Total                : 0.54
% 2.30/1.32  Index Insertion      : 0.00
% 2.30/1.32  Index Deletion       : 0.00
% 2.30/1.32  Index Matching       : 0.00
% 2.30/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------

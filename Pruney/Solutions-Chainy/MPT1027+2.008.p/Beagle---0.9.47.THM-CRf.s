%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:43 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 283 expanded)
%              Number of leaves         :   28 ( 108 expanded)
%              Depth                    :   12
%              Number of atoms          :  116 ( 732 expanded)
%              Number of equality atoms :   38 ( 190 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_63,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_34,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_16,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_1'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_42,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_50,plain,(
    ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42])).

tff(c_44,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_281,plain,(
    ! [B_71,C_72,A_73] :
      ( k1_xboole_0 = B_71
      | v1_funct_2(C_72,A_73,B_71)
      | k1_relset_1(A_73,B_71,C_72) != A_73
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_287,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_46,c_281])).

tff(c_301,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_287])).

tff(c_302,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_301])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_324,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_2])).

tff(c_6,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_321,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_302,c_6])).

tff(c_107,plain,(
    ! [C_36,B_37,A_38] :
      ( ~ v1_xboole_0(C_36)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(C_36))
      | ~ r2_hidden(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_120,plain,(
    ! [A_38] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_38,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_46,c_107])).

tff(c_149,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_376,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_149])).

tff(c_380,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_376])).

tff(c_383,plain,(
    ! [A_79] : ~ r2_hidden(A_79,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_388,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_16,c_383])).

tff(c_86,plain,(
    ! [A_33] : m1_subset_1(k6_partfun1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_90,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_86])).

tff(c_109,plain,(
    ! [A_38] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_38,k6_partfun1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_90,c_107])).

tff(c_122,plain,(
    ! [A_39] : ~ r2_hidden(A_39,k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_109])).

tff(c_127,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_122])).

tff(c_390,plain,(
    k6_partfun1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_388,c_127])).

tff(c_38,plain,(
    ! [A_26] : v1_partfun1(k6_partfun1(A_26),A_26) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_40,plain,(
    ! [A_26] : m1_subset_1(k6_partfun1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_494,plain,(
    ! [C_96,A_97,B_98] :
      ( v1_funct_2(C_96,A_97,B_98)
      | ~ v1_partfun1(C_96,A_97)
      | ~ v1_funct_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_507,plain,(
    ! [A_26] :
      ( v1_funct_2(k6_partfun1(A_26),A_26,A_26)
      | ~ v1_partfun1(k6_partfun1(A_26),A_26)
      | ~ v1_funct_1(k6_partfun1(A_26)) ) ),
    inference(resolution,[status(thm)],[c_40,c_494])).

tff(c_519,plain,(
    ! [A_101] :
      ( v1_funct_2(k6_partfun1(A_101),A_101,A_101)
      | ~ v1_funct_1(k6_partfun1(A_101)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_507])).

tff(c_522,plain,
    ( v1_funct_2('#skF_4','#skF_4','#skF_4')
    | ~ v1_funct_1(k6_partfun1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_519])).

tff(c_524,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_390,c_522])).

tff(c_10,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_26,plain,(
    ! [A_23] :
      ( v1_funct_2(k1_xboole_0,A_23,k1_xboole_0)
      | k1_xboole_0 = A_23
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_23,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_52,plain,(
    ! [A_23] :
      ( v1_funct_2(k1_xboole_0,A_23,k1_xboole_0)
      | k1_xboole_0 = A_23 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_26])).

tff(c_392,plain,(
    ! [A_23] :
      ( v1_funct_2('#skF_4',A_23,'#skF_4')
      | A_23 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_388,c_388,c_52])).

tff(c_396,plain,(
    ! [A_3] : m1_subset_1('#skF_4',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_10])).

tff(c_32,plain,(
    ! [B_24,C_25,A_23] :
      ( k1_xboole_0 = B_24
      | v1_funct_2(C_25,A_23,B_24)
      | k1_relset_1(A_23,B_24,C_25) != A_23
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_575,plain,(
    ! [B_112,C_113,A_114] :
      ( B_112 = '#skF_4'
      | v1_funct_2(C_113,A_114,B_112)
      | k1_relset_1(A_114,B_112,C_113) != A_114
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_114,B_112))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_32])).

tff(c_607,plain,(
    ! [B_116,A_117] :
      ( B_116 = '#skF_4'
      | v1_funct_2('#skF_4',A_117,B_116)
      | k1_relset_1(A_117,B_116,'#skF_4') != A_117 ) ),
    inference(resolution,[status(thm)],[c_396,c_575])).

tff(c_613,plain,
    ( '#skF_3' = '#skF_4'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_607,c_50])).

tff(c_620,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_613])).

tff(c_623,plain,(
    ~ v1_funct_2('#skF_4','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_620,c_50])).

tff(c_641,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_392,c_623])).

tff(c_642,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_623])).

tff(c_646,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_642])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:42:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.44  
% 2.87/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.44  %$ v1_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.87/1.44  
% 2.87/1.44  %Foreground sorts:
% 2.87/1.44  
% 2.87/1.44  
% 2.87/1.44  %Background operators:
% 2.87/1.44  
% 2.87/1.44  
% 2.87/1.44  %Foreground operators:
% 2.87/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.87/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.44  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.87/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.87/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.87/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.87/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.87/1.44  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.87/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.87/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.87/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.87/1.44  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.87/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.87/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.87/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.87/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.87/1.44  
% 2.87/1.46  tff(f_108, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_funct_2)).
% 2.87/1.46  tff(f_63, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.87/1.46  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.87/1.46  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.87/1.46  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.87/1.46  tff(f_47, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.87/1.46  tff(f_95, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.87/1.46  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 2.87/1.46  tff(f_34, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.87/1.46  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.87/1.46  tff(c_16, plain, (![A_10]: (r2_hidden('#skF_1'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.87/1.46  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.87/1.46  tff(c_42, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.87/1.46  tff(c_50, plain, (~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42])).
% 2.87/1.46  tff(c_44, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.87/1.46  tff(c_281, plain, (![B_71, C_72, A_73]: (k1_xboole_0=B_71 | v1_funct_2(C_72, A_73, B_71) | k1_relset_1(A_73, B_71, C_72)!=A_73 | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_71))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.87/1.46  tff(c_287, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(resolution, [status(thm)], [c_46, c_281])).
% 2.87/1.46  tff(c_301, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_287])).
% 2.87/1.46  tff(c_302, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_50, c_301])).
% 2.87/1.46  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.87/1.46  tff(c_324, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_302, c_2])).
% 2.87/1.46  tff(c_6, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.87/1.46  tff(c_321, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_302, c_302, c_6])).
% 2.87/1.46  tff(c_107, plain, (![C_36, B_37, A_38]: (~v1_xboole_0(C_36) | ~m1_subset_1(B_37, k1_zfmisc_1(C_36)) | ~r2_hidden(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.87/1.46  tff(c_120, plain, (![A_38]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_38, '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_107])).
% 2.87/1.46  tff(c_149, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_120])).
% 2.87/1.46  tff(c_376, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_321, c_149])).
% 2.87/1.46  tff(c_380, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_324, c_376])).
% 2.87/1.46  tff(c_383, plain, (![A_79]: (~r2_hidden(A_79, '#skF_4'))), inference(splitRight, [status(thm)], [c_120])).
% 2.87/1.46  tff(c_388, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_16, c_383])).
% 2.87/1.46  tff(c_86, plain, (![A_33]: (m1_subset_1(k6_partfun1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.87/1.46  tff(c_90, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_86])).
% 2.87/1.46  tff(c_109, plain, (![A_38]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_38, k6_partfun1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_90, c_107])).
% 2.87/1.46  tff(c_122, plain, (![A_39]: (~r2_hidden(A_39, k6_partfun1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_109])).
% 2.87/1.46  tff(c_127, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_122])).
% 2.87/1.46  tff(c_390, plain, (k6_partfun1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_388, c_388, c_127])).
% 2.87/1.46  tff(c_38, plain, (![A_26]: (v1_partfun1(k6_partfun1(A_26), A_26))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.87/1.46  tff(c_40, plain, (![A_26]: (m1_subset_1(k6_partfun1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.87/1.46  tff(c_494, plain, (![C_96, A_97, B_98]: (v1_funct_2(C_96, A_97, B_98) | ~v1_partfun1(C_96, A_97) | ~v1_funct_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.87/1.46  tff(c_507, plain, (![A_26]: (v1_funct_2(k6_partfun1(A_26), A_26, A_26) | ~v1_partfun1(k6_partfun1(A_26), A_26) | ~v1_funct_1(k6_partfun1(A_26)))), inference(resolution, [status(thm)], [c_40, c_494])).
% 2.87/1.46  tff(c_519, plain, (![A_101]: (v1_funct_2(k6_partfun1(A_101), A_101, A_101) | ~v1_funct_1(k6_partfun1(A_101)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_507])).
% 2.87/1.46  tff(c_522, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4') | ~v1_funct_1(k6_partfun1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_390, c_519])).
% 2.87/1.46  tff(c_524, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_390, c_522])).
% 2.87/1.46  tff(c_10, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.87/1.46  tff(c_26, plain, (![A_23]: (v1_funct_2(k1_xboole_0, A_23, k1_xboole_0) | k1_xboole_0=A_23 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_23, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.87/1.46  tff(c_52, plain, (![A_23]: (v1_funct_2(k1_xboole_0, A_23, k1_xboole_0) | k1_xboole_0=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_26])).
% 2.87/1.46  tff(c_392, plain, (![A_23]: (v1_funct_2('#skF_4', A_23, '#skF_4') | A_23='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_388, c_388, c_388, c_52])).
% 2.87/1.46  tff(c_396, plain, (![A_3]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_388, c_10])).
% 2.87/1.46  tff(c_32, plain, (![B_24, C_25, A_23]: (k1_xboole_0=B_24 | v1_funct_2(C_25, A_23, B_24) | k1_relset_1(A_23, B_24, C_25)!=A_23 | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.87/1.46  tff(c_575, plain, (![B_112, C_113, A_114]: (B_112='#skF_4' | v1_funct_2(C_113, A_114, B_112) | k1_relset_1(A_114, B_112, C_113)!=A_114 | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_114, B_112))))), inference(demodulation, [status(thm), theory('equality')], [c_388, c_32])).
% 2.87/1.46  tff(c_607, plain, (![B_116, A_117]: (B_116='#skF_4' | v1_funct_2('#skF_4', A_117, B_116) | k1_relset_1(A_117, B_116, '#skF_4')!=A_117)), inference(resolution, [status(thm)], [c_396, c_575])).
% 2.87/1.46  tff(c_613, plain, ('#skF_3'='#skF_4' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(resolution, [status(thm)], [c_607, c_50])).
% 2.87/1.46  tff(c_620, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_613])).
% 2.87/1.46  tff(c_623, plain, (~v1_funct_2('#skF_4', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_620, c_50])).
% 2.87/1.46  tff(c_641, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_392, c_623])).
% 2.87/1.46  tff(c_642, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_641, c_623])).
% 2.87/1.46  tff(c_646, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_524, c_642])).
% 2.87/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.46  
% 2.87/1.46  Inference rules
% 2.87/1.46  ----------------------
% 2.87/1.46  #Ref     : 0
% 2.87/1.46  #Sup     : 118
% 2.87/1.46  #Fact    : 0
% 2.87/1.46  #Define  : 0
% 2.87/1.46  #Split   : 1
% 2.87/1.46  #Chain   : 0
% 2.87/1.46  #Close   : 0
% 2.87/1.46  
% 2.87/1.46  Ordering : KBO
% 2.87/1.46  
% 2.87/1.46  Simplification rules
% 2.87/1.46  ----------------------
% 2.87/1.46  #Subsume      : 18
% 2.87/1.46  #Demod        : 155
% 2.87/1.46  #Tautology    : 62
% 2.87/1.46  #SimpNegUnit  : 2
% 2.87/1.46  #BackRed      : 39
% 2.87/1.46  
% 2.87/1.46  #Partial instantiations: 0
% 2.87/1.46  #Strategies tried      : 1
% 2.87/1.46  
% 2.87/1.46  Timing (in seconds)
% 2.87/1.46  ----------------------
% 2.87/1.46  Preprocessing        : 0.36
% 2.87/1.46  Parsing              : 0.18
% 2.87/1.46  CNF conversion       : 0.03
% 2.87/1.46  Main loop            : 0.34
% 2.87/1.46  Inferencing          : 0.12
% 2.87/1.46  Reduction            : 0.11
% 2.87/1.46  Demodulation         : 0.08
% 2.87/1.46  BG Simplification    : 0.03
% 2.87/1.46  Subsumption          : 0.06
% 2.87/1.46  Abstraction          : 0.02
% 2.87/1.46  MUC search           : 0.00
% 2.87/1.46  Cooper               : 0.00
% 2.87/1.46  Total                : 0.73
% 2.87/1.46  Index Insertion      : 0.00
% 2.87/1.46  Index Deletion       : 0.00
% 2.87/1.46  Index Matching       : 0.00
% 2.87/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------

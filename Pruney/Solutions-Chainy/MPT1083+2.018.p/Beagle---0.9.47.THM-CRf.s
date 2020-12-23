%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:19 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   62 (  97 expanded)
%              Number of leaves         :   30 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :   98 ( 232 expanded)
%              Number of equality atoms :   18 (  33 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_101,negated_conjecture,(
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

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_30,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_42,plain,(
    ! [B_25,A_26] :
      ( v1_relat_1(B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_26))
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_45,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_34,c_42])).

tff(c_48,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_45])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_50,plain,(
    ! [C_29,A_30,B_31] :
      ( v4_relat_1(C_29,A_30)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_54,plain,(
    v4_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_50])).

tff(c_66,plain,(
    ! [B_38,A_39] :
      ( k1_relat_1(B_38) = A_39
      | ~ v1_partfun1(B_38,A_39)
      | ~ v4_relat_1(B_38,A_39)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_69,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_66])).

tff(c_72,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_69])).

tff(c_73,plain,(
    ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_38,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_36,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_82,plain,(
    ! [B_46,C_47,A_48] :
      ( k1_xboole_0 = B_46
      | v1_partfun1(C_47,A_48)
      | ~ v1_funct_2(C_47,A_48,B_46)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_46)))
      | ~ v1_funct_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_85,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_partfun1('#skF_2','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_82])).

tff(c_88,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_partfun1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_85])).

tff(c_89,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_88])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_92,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_2])).

tff(c_94,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_92])).

tff(c_95,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_107,plain,(
    ! [A_49,B_50] :
      ( k1_relat_1(k5_relat_1(A_49,B_50)) = k1_relat_1(A_49)
      | ~ r1_tarski(k2_relat_1(A_49),k1_relat_1(B_50))
      | ~ v1_relat_1(B_50)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_110,plain,(
    ! [A_49] :
      ( k1_relat_1(k5_relat_1(A_49,'#skF_2')) = k1_relat_1(A_49)
      | ~ r1_tarski(k2_relat_1(A_49),'#skF_1')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_107])).

tff(c_118,plain,(
    ! [A_51] :
      ( k1_relat_1(k5_relat_1(A_51,'#skF_2')) = k1_relat_1(A_51)
      | ~ r1_tarski(k2_relat_1(A_51),'#skF_1')
      | ~ v1_relat_1(A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_110])).

tff(c_124,plain,(
    ! [B_52] :
      ( k1_relat_1(k5_relat_1(B_52,'#skF_2')) = k1_relat_1(B_52)
      | ~ v5_relat_1(B_52,'#skF_1')
      | ~ v1_relat_1(B_52) ) ),
    inference(resolution,[status(thm)],[c_8,c_118])).

tff(c_26,plain,(
    k1_relat_1(k5_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_136,plain,
    ( ~ v5_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_26])).

tff(c_144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:56:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.24  
% 2.17/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.24  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.17/1.24  
% 2.17/1.24  %Foreground sorts:
% 2.17/1.24  
% 2.17/1.24  
% 2.17/1.24  %Background operators:
% 2.17/1.24  
% 2.17/1.24  
% 2.17/1.24  %Foreground operators:
% 2.17/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.17/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.24  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.17/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.17/1.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.17/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.24  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.17/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.24  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.17/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.17/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.24  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.17/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.17/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.24  
% 2.17/1.25  tff(f_101, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (k1_relat_1(k5_relat_1(C, B)) = k1_relat_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t200_funct_2)).
% 2.17/1.25  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.17/1.25  tff(f_41, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.17/1.25  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.17/1.25  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.17/1.25  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 2.17/1.25  tff(f_81, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 2.17/1.25  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.17/1.25  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 2.17/1.25  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.17/1.25  tff(c_30, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.17/1.25  tff(c_8, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.17/1.25  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.17/1.25  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.17/1.25  tff(c_42, plain, (![B_25, A_26]: (v1_relat_1(B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(A_26)) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.17/1.25  tff(c_45, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_34, c_42])).
% 2.17/1.25  tff(c_48, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_45])).
% 2.17/1.25  tff(c_40, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.17/1.25  tff(c_50, plain, (![C_29, A_30, B_31]: (v4_relat_1(C_29, A_30) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.17/1.25  tff(c_54, plain, (v4_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_50])).
% 2.17/1.25  tff(c_66, plain, (![B_38, A_39]: (k1_relat_1(B_38)=A_39 | ~v1_partfun1(B_38, A_39) | ~v4_relat_1(B_38, A_39) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.17/1.25  tff(c_69, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v1_partfun1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_54, c_66])).
% 2.17/1.25  tff(c_72, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v1_partfun1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_69])).
% 2.17/1.25  tff(c_73, plain, (~v1_partfun1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_72])).
% 2.17/1.25  tff(c_38, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.17/1.25  tff(c_36, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.17/1.25  tff(c_82, plain, (![B_46, C_47, A_48]: (k1_xboole_0=B_46 | v1_partfun1(C_47, A_48) | ~v1_funct_2(C_47, A_48, B_46) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_46))) | ~v1_funct_1(C_47))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.17/1.25  tff(c_85, plain, (k1_xboole_0='#skF_1' | v1_partfun1('#skF_2', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_34, c_82])).
% 2.17/1.25  tff(c_88, plain, (k1_xboole_0='#skF_1' | v1_partfun1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_85])).
% 2.17/1.25  tff(c_89, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_73, c_88])).
% 2.17/1.25  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.17/1.25  tff(c_92, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_2])).
% 2.17/1.25  tff(c_94, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_92])).
% 2.17/1.25  tff(c_95, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_72])).
% 2.17/1.25  tff(c_107, plain, (![A_49, B_50]: (k1_relat_1(k5_relat_1(A_49, B_50))=k1_relat_1(A_49) | ~r1_tarski(k2_relat_1(A_49), k1_relat_1(B_50)) | ~v1_relat_1(B_50) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.17/1.25  tff(c_110, plain, (![A_49]: (k1_relat_1(k5_relat_1(A_49, '#skF_2'))=k1_relat_1(A_49) | ~r1_tarski(k2_relat_1(A_49), '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(A_49))), inference(superposition, [status(thm), theory('equality')], [c_95, c_107])).
% 2.17/1.25  tff(c_118, plain, (![A_51]: (k1_relat_1(k5_relat_1(A_51, '#skF_2'))=k1_relat_1(A_51) | ~r1_tarski(k2_relat_1(A_51), '#skF_1') | ~v1_relat_1(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_110])).
% 2.17/1.25  tff(c_124, plain, (![B_52]: (k1_relat_1(k5_relat_1(B_52, '#skF_2'))=k1_relat_1(B_52) | ~v5_relat_1(B_52, '#skF_1') | ~v1_relat_1(B_52))), inference(resolution, [status(thm)], [c_8, c_118])).
% 2.17/1.25  tff(c_26, plain, (k1_relat_1(k5_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.17/1.25  tff(c_136, plain, (~v5_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_124, c_26])).
% 2.17/1.25  tff(c_144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_136])).
% 2.17/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.25  
% 2.17/1.25  Inference rules
% 2.17/1.25  ----------------------
% 2.17/1.25  #Ref     : 0
% 2.17/1.25  #Sup     : 18
% 2.17/1.25  #Fact    : 0
% 2.17/1.25  #Define  : 0
% 2.17/1.25  #Split   : 1
% 2.17/1.25  #Chain   : 0
% 2.17/1.25  #Close   : 0
% 2.17/1.25  
% 2.17/1.25  Ordering : KBO
% 2.17/1.25  
% 2.17/1.25  Simplification rules
% 2.17/1.25  ----------------------
% 2.17/1.25  #Subsume      : 0
% 2.17/1.25  #Demod        : 16
% 2.17/1.25  #Tautology    : 5
% 2.17/1.25  #SimpNegUnit  : 2
% 2.17/1.25  #BackRed      : 3
% 2.17/1.25  
% 2.17/1.25  #Partial instantiations: 0
% 2.17/1.25  #Strategies tried      : 1
% 2.17/1.25  
% 2.17/1.25  Timing (in seconds)
% 2.17/1.25  ----------------------
% 2.17/1.26  Preprocessing        : 0.30
% 2.17/1.26  Parsing              : 0.16
% 2.17/1.26  CNF conversion       : 0.02
% 2.17/1.26  Main loop            : 0.19
% 2.17/1.26  Inferencing          : 0.07
% 2.17/1.26  Reduction            : 0.06
% 2.17/1.26  Demodulation         : 0.04
% 2.17/1.26  BG Simplification    : 0.01
% 2.17/1.26  Subsumption          : 0.03
% 2.17/1.26  Abstraction          : 0.01
% 2.17/1.26  MUC search           : 0.00
% 2.17/1.26  Cooper               : 0.00
% 2.17/1.26  Total                : 0.52
% 2.17/1.26  Index Insertion      : 0.00
% 2.17/1.26  Index Deletion       : 0.00
% 2.17/1.26  Index Matching       : 0.00
% 2.17/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------

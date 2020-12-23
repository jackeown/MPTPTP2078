%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:19 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   57 (  92 expanded)
%              Number of leaves         :   28 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :   92 ( 226 expanded)
%              Number of equality atoms :   12 (  27 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_97,negated_conjecture,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_28,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_40,plain,(
    ! [B_26,A_27] :
      ( v1_relat_1(B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_27))
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_43,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_40])).

tff(c_46,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_43])).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_58,plain,(
    ! [C_35,A_36,B_37] :
      ( v4_relat_1(C_35,A_36)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_62,plain,(
    v4_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_58])).

tff(c_64,plain,(
    ! [B_39,A_40] :
      ( k1_relat_1(B_39) = A_40
      | ~ v1_partfun1(B_39,A_40)
      | ~ v4_relat_1(B_39,A_40)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_67,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_64])).

tff(c_70,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_67])).

tff(c_71,plain,(
    ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_36,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_34,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_79,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_partfun1(C_45,A_46)
      | ~ v1_funct_2(C_45,A_46,B_47)
      | ~ v1_funct_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47)))
      | v1_xboole_0(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_82,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_79])).

tff(c_85,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_82])).

tff(c_87,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_71,c_85])).

tff(c_88,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_99,plain,(
    ! [A_48,B_49] :
      ( k1_relat_1(k5_relat_1(A_48,B_49)) = k1_relat_1(A_48)
      | ~ r1_tarski(k2_relat_1(A_48),k1_relat_1(B_49))
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_102,plain,(
    ! [A_48] :
      ( k1_relat_1(k5_relat_1(A_48,'#skF_2')) = k1_relat_1(A_48)
      | ~ r1_tarski(k2_relat_1(A_48),'#skF_1')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_99])).

tff(c_111,plain,(
    ! [A_50] :
      ( k1_relat_1(k5_relat_1(A_50,'#skF_2')) = k1_relat_1(A_50)
      | ~ r1_tarski(k2_relat_1(A_50),'#skF_1')
      | ~ v1_relat_1(A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_102])).

tff(c_117,plain,(
    ! [B_51] :
      ( k1_relat_1(k5_relat_1(B_51,'#skF_2')) = k1_relat_1(B_51)
      | ~ v5_relat_1(B_51,'#skF_1')
      | ~ v1_relat_1(B_51) ) ),
    inference(resolution,[status(thm)],[c_6,c_111])).

tff(c_24,plain,(
    k1_relat_1(k5_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_129,plain,
    ( ~ v5_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_24])).

tff(c_137,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_129])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.30  % Computer   : n009.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.30  % DateTime   : Tue Dec  1 12:00:26 EST 2020
% 0.11/0.30  % CPUTime    : 
% 0.16/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.09  
% 1.90/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.10  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.90/1.10  
% 1.90/1.10  %Foreground sorts:
% 1.90/1.10  
% 1.90/1.10  
% 1.90/1.10  %Background operators:
% 1.90/1.10  
% 1.90/1.10  
% 1.90/1.10  %Foreground operators:
% 1.90/1.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.90/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.10  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.90/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.90/1.10  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.90/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.90/1.10  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.90/1.10  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.90/1.10  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.90/1.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.90/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.90/1.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.90/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.10  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.90/1.10  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.90/1.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.90/1.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.90/1.10  
% 1.90/1.11  tff(f_97, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (k1_relat_1(k5_relat_1(C, B)) = k1_relat_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t200_funct_2)).
% 1.90/1.11  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 1.90/1.11  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.90/1.11  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.90/1.11  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.90/1.11  tff(f_77, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 1.90/1.11  tff(f_69, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 1.90/1.11  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 1.90/1.11  tff(c_30, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 1.90/1.11  tff(c_28, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 1.90/1.11  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.90/1.11  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.90/1.11  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 1.90/1.11  tff(c_40, plain, (![B_26, A_27]: (v1_relat_1(B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(A_27)) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.90/1.11  tff(c_43, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_32, c_40])).
% 1.90/1.11  tff(c_46, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_43])).
% 1.90/1.11  tff(c_38, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 1.90/1.11  tff(c_58, plain, (![C_35, A_36, B_37]: (v4_relat_1(C_35, A_36) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.90/1.11  tff(c_62, plain, (v4_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_58])).
% 1.90/1.11  tff(c_64, plain, (![B_39, A_40]: (k1_relat_1(B_39)=A_40 | ~v1_partfun1(B_39, A_40) | ~v4_relat_1(B_39, A_40) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.90/1.11  tff(c_67, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v1_partfun1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_64])).
% 1.90/1.11  tff(c_70, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v1_partfun1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_67])).
% 1.90/1.11  tff(c_71, plain, (~v1_partfun1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_70])).
% 1.90/1.11  tff(c_36, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 1.90/1.11  tff(c_34, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 1.90/1.11  tff(c_79, plain, (![C_45, A_46, B_47]: (v1_partfun1(C_45, A_46) | ~v1_funct_2(C_45, A_46, B_47) | ~v1_funct_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))) | v1_xboole_0(B_47))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.90/1.11  tff(c_82, plain, (v1_partfun1('#skF_2', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_79])).
% 1.90/1.11  tff(c_85, plain, (v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_82])).
% 1.90/1.11  tff(c_87, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_71, c_85])).
% 1.90/1.11  tff(c_88, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_70])).
% 1.90/1.11  tff(c_99, plain, (![A_48, B_49]: (k1_relat_1(k5_relat_1(A_48, B_49))=k1_relat_1(A_48) | ~r1_tarski(k2_relat_1(A_48), k1_relat_1(B_49)) | ~v1_relat_1(B_49) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.90/1.11  tff(c_102, plain, (![A_48]: (k1_relat_1(k5_relat_1(A_48, '#skF_2'))=k1_relat_1(A_48) | ~r1_tarski(k2_relat_1(A_48), '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(A_48))), inference(superposition, [status(thm), theory('equality')], [c_88, c_99])).
% 1.90/1.11  tff(c_111, plain, (![A_50]: (k1_relat_1(k5_relat_1(A_50, '#skF_2'))=k1_relat_1(A_50) | ~r1_tarski(k2_relat_1(A_50), '#skF_1') | ~v1_relat_1(A_50))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_102])).
% 1.90/1.11  tff(c_117, plain, (![B_51]: (k1_relat_1(k5_relat_1(B_51, '#skF_2'))=k1_relat_1(B_51) | ~v5_relat_1(B_51, '#skF_1') | ~v1_relat_1(B_51))), inference(resolution, [status(thm)], [c_6, c_111])).
% 1.90/1.11  tff(c_24, plain, (k1_relat_1(k5_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 1.90/1.11  tff(c_129, plain, (~v5_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_117, c_24])).
% 1.90/1.11  tff(c_137, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_129])).
% 1.90/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.11  
% 1.90/1.11  Inference rules
% 1.90/1.11  ----------------------
% 1.90/1.11  #Ref     : 0
% 1.90/1.11  #Sup     : 18
% 1.90/1.11  #Fact    : 0
% 1.90/1.11  #Define  : 0
% 1.90/1.11  #Split   : 1
% 1.90/1.11  #Chain   : 0
% 1.90/1.11  #Close   : 0
% 1.90/1.11  
% 1.90/1.11  Ordering : KBO
% 1.90/1.11  
% 1.90/1.11  Simplification rules
% 1.90/1.11  ----------------------
% 1.90/1.11  #Subsume      : 0
% 1.90/1.11  #Demod        : 11
% 1.90/1.11  #Tautology    : 6
% 1.90/1.11  #SimpNegUnit  : 1
% 1.90/1.11  #BackRed      : 0
% 1.90/1.11  
% 1.90/1.11  #Partial instantiations: 0
% 1.90/1.11  #Strategies tried      : 1
% 1.90/1.11  
% 1.90/1.11  Timing (in seconds)
% 1.90/1.11  ----------------------
% 1.90/1.11  Preprocessing        : 0.29
% 1.90/1.11  Parsing              : 0.16
% 1.90/1.11  CNF conversion       : 0.02
% 1.90/1.11  Main loop            : 0.15
% 1.90/1.11  Inferencing          : 0.06
% 1.90/1.11  Reduction            : 0.04
% 1.90/1.11  Demodulation         : 0.03
% 1.90/1.11  BG Simplification    : 0.01
% 1.90/1.11  Subsumption          : 0.02
% 1.90/1.11  Abstraction          : 0.01
% 1.90/1.11  MUC search           : 0.00
% 1.90/1.11  Cooper               : 0.00
% 1.90/1.11  Total                : 0.47
% 1.90/1.11  Index Insertion      : 0.00
% 1.90/1.11  Index Deletion       : 0.00
% 1.90/1.11  Index Matching       : 0.00
% 1.90/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------

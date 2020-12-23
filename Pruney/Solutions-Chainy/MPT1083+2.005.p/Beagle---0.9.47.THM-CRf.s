%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:17 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   54 (  83 expanded)
%              Number of leaves         :   27 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :   86 ( 208 expanded)
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

tff(f_92,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_26,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_37,plain,(
    ! [C_22,A_23,B_24] :
      ( v1_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_41,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_37])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_48,plain,(
    ! [C_30,A_31,B_32] :
      ( v4_relat_1(C_30,A_31)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_52,plain,(
    v4_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_48])).

tff(c_59,plain,(
    ! [B_36,A_37] :
      ( k1_relat_1(B_36) = A_37
      | ~ v1_partfun1(B_36,A_37)
      | ~ v4_relat_1(B_36,A_37)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_62,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_59])).

tff(c_65,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_62])).

tff(c_66,plain,(
    ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_34,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_32,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_74,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_partfun1(C_42,A_43)
      | ~ v1_funct_2(C_42,A_43,B_44)
      | ~ v1_funct_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44)))
      | v1_xboole_0(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_77,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_74])).

tff(c_80,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_77])).

tff(c_82,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_66,c_80])).

tff(c_83,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_94,plain,(
    ! [A_45,B_46] :
      ( k1_relat_1(k5_relat_1(A_45,B_46)) = k1_relat_1(A_45)
      | ~ r1_tarski(k2_relat_1(A_45),k1_relat_1(B_46))
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_97,plain,(
    ! [A_45] :
      ( k1_relat_1(k5_relat_1(A_45,'#skF_2')) = k1_relat_1(A_45)
      | ~ r1_tarski(k2_relat_1(A_45),'#skF_1')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(A_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_94])).

tff(c_106,plain,(
    ! [A_47] :
      ( k1_relat_1(k5_relat_1(A_47,'#skF_2')) = k1_relat_1(A_47)
      | ~ r1_tarski(k2_relat_1(A_47),'#skF_1')
      | ~ v1_relat_1(A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_97])).

tff(c_112,plain,(
    ! [B_48] :
      ( k1_relat_1(k5_relat_1(B_48,'#skF_2')) = k1_relat_1(B_48)
      | ~ v5_relat_1(B_48,'#skF_1')
      | ~ v1_relat_1(B_48) ) ),
    inference(resolution,[status(thm)],[c_4,c_106])).

tff(c_22,plain,(
    k1_relat_1(k5_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_124,plain,
    ( ~ v5_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_22])).

tff(c_132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_124])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:13:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.27  
% 2.03/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.28  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.03/1.28  
% 2.03/1.28  %Foreground sorts:
% 2.03/1.28  
% 2.03/1.28  
% 2.03/1.28  %Background operators:
% 2.03/1.28  
% 2.03/1.28  
% 2.03/1.28  %Foreground operators:
% 2.03/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.03/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.28  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.03/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.03/1.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.03/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.03/1.28  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.03/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.03/1.28  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.03/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.03/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.03/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.03/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.28  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.03/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.03/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.03/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.03/1.28  
% 2.03/1.29  tff(f_92, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (k1_relat_1(k5_relat_1(C, B)) = k1_relat_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t200_funct_2)).
% 2.03/1.29  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.03/1.29  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.03/1.29  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.03/1.29  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 2.03/1.29  tff(f_64, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.03/1.29  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 2.03/1.29  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.03/1.29  tff(c_26, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.03/1.29  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.03/1.29  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.03/1.29  tff(c_37, plain, (![C_22, A_23, B_24]: (v1_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.03/1.29  tff(c_41, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_30, c_37])).
% 2.03/1.29  tff(c_36, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.03/1.29  tff(c_48, plain, (![C_30, A_31, B_32]: (v4_relat_1(C_30, A_31) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.03/1.29  tff(c_52, plain, (v4_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_48])).
% 2.03/1.29  tff(c_59, plain, (![B_36, A_37]: (k1_relat_1(B_36)=A_37 | ~v1_partfun1(B_36, A_37) | ~v4_relat_1(B_36, A_37) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.03/1.29  tff(c_62, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v1_partfun1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_59])).
% 2.03/1.29  tff(c_65, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v1_partfun1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_41, c_62])).
% 2.03/1.29  tff(c_66, plain, (~v1_partfun1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_65])).
% 2.03/1.29  tff(c_34, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.03/1.29  tff(c_32, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.03/1.29  tff(c_74, plain, (![C_42, A_43, B_44]: (v1_partfun1(C_42, A_43) | ~v1_funct_2(C_42, A_43, B_44) | ~v1_funct_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))) | v1_xboole_0(B_44))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.03/1.29  tff(c_77, plain, (v1_partfun1('#skF_2', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_74])).
% 2.03/1.29  tff(c_80, plain, (v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_77])).
% 2.03/1.29  tff(c_82, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_66, c_80])).
% 2.03/1.29  tff(c_83, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_65])).
% 2.03/1.29  tff(c_94, plain, (![A_45, B_46]: (k1_relat_1(k5_relat_1(A_45, B_46))=k1_relat_1(A_45) | ~r1_tarski(k2_relat_1(A_45), k1_relat_1(B_46)) | ~v1_relat_1(B_46) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.03/1.29  tff(c_97, plain, (![A_45]: (k1_relat_1(k5_relat_1(A_45, '#skF_2'))=k1_relat_1(A_45) | ~r1_tarski(k2_relat_1(A_45), '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(A_45))), inference(superposition, [status(thm), theory('equality')], [c_83, c_94])).
% 2.03/1.29  tff(c_106, plain, (![A_47]: (k1_relat_1(k5_relat_1(A_47, '#skF_2'))=k1_relat_1(A_47) | ~r1_tarski(k2_relat_1(A_47), '#skF_1') | ~v1_relat_1(A_47))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_97])).
% 2.03/1.29  tff(c_112, plain, (![B_48]: (k1_relat_1(k5_relat_1(B_48, '#skF_2'))=k1_relat_1(B_48) | ~v5_relat_1(B_48, '#skF_1') | ~v1_relat_1(B_48))), inference(resolution, [status(thm)], [c_4, c_106])).
% 2.03/1.29  tff(c_22, plain, (k1_relat_1(k5_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.03/1.29  tff(c_124, plain, (~v5_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_112, c_22])).
% 2.03/1.29  tff(c_132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_124])).
% 2.03/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.29  
% 2.03/1.29  Inference rules
% 2.03/1.29  ----------------------
% 2.03/1.29  #Ref     : 0
% 2.03/1.29  #Sup     : 18
% 2.03/1.29  #Fact    : 0
% 2.03/1.29  #Define  : 0
% 2.03/1.29  #Split   : 1
% 2.03/1.29  #Chain   : 0
% 2.03/1.29  #Close   : 0
% 2.03/1.29  
% 2.03/1.29  Ordering : KBO
% 2.03/1.29  
% 2.03/1.29  Simplification rules
% 2.03/1.29  ----------------------
% 2.03/1.29  #Subsume      : 0
% 2.03/1.29  #Demod        : 10
% 2.03/1.29  #Tautology    : 6
% 2.03/1.29  #SimpNegUnit  : 1
% 2.03/1.29  #BackRed      : 0
% 2.03/1.29  
% 2.03/1.29  #Partial instantiations: 0
% 2.03/1.29  #Strategies tried      : 1
% 2.03/1.29  
% 2.03/1.29  Timing (in seconds)
% 2.03/1.29  ----------------------
% 2.03/1.29  Preprocessing        : 0.27
% 2.03/1.29  Parsing              : 0.15
% 2.03/1.29  CNF conversion       : 0.02
% 2.03/1.29  Main loop            : 0.17
% 2.03/1.29  Inferencing          : 0.07
% 2.03/1.29  Reduction            : 0.05
% 2.03/1.29  Demodulation         : 0.03
% 2.03/1.29  BG Simplification    : 0.01
% 2.03/1.30  Subsumption          : 0.02
% 2.03/1.30  Abstraction          : 0.01
% 2.03/1.30  MUC search           : 0.00
% 2.03/1.30  Cooper               : 0.00
% 2.03/1.30  Total                : 0.47
% 2.03/1.30  Index Insertion      : 0.00
% 2.03/1.30  Index Deletion       : 0.00
% 2.03/1.30  Index Matching       : 0.00
% 2.03/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------

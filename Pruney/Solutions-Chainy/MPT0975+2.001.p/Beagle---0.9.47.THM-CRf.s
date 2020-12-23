%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:45 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   46 (  57 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   71 ( 145 expanded)
%              Number of equality atoms :   24 (  42 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ( ( v1_relat_1(E)
              & v1_funct_1(E) )
           => ( r2_hidden(C,A)
             => ( B = k1_xboole_0
                | k1_funct_1(k5_relat_1(D,E),C) = k1_funct_1(E,k1_funct_1(D,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_2)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_64,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_26,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_24,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_35,plain,(
    ! [C_15,A_16,B_17] :
      ( v1_relat_1(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_39,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_35])).

tff(c_34,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_32,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_41,plain,(
    ! [A_19,B_20,C_21] :
      ( k1_relset_1(A_19,B_20,C_21) = k1_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_45,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_41])).

tff(c_53,plain,(
    ! [B_28,A_29,C_30] :
      ( k1_xboole_0 = B_28
      | k1_relset_1(A_29,B_28,C_30) = A_29
      | ~ v1_funct_2(C_30,A_29,B_28)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_29,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_56,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_53])).

tff(c_59,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_45,c_56])).

tff(c_60,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_59])).

tff(c_78,plain,(
    ! [B_34,C_35,A_36] :
      ( k1_funct_1(k5_relat_1(B_34,C_35),A_36) = k1_funct_1(C_35,k1_funct_1(B_34,A_36))
      | ~ r2_hidden(A_36,k1_relat_1(B_34))
      | ~ v1_funct_1(C_35)
      | ~ v1_relat_1(C_35)
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_80,plain,(
    ! [C_35,A_36] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_35),A_36) = k1_funct_1(C_35,k1_funct_1('#skF_4',A_36))
      | ~ r2_hidden(A_36,'#skF_1')
      | ~ v1_funct_1(C_35)
      | ~ v1_relat_1(C_35)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_78])).

tff(c_83,plain,(
    ! [C_37,A_38] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_37),A_38) = k1_funct_1(C_37,k1_funct_1('#skF_4',A_38))
      | ~ r2_hidden(A_38,'#skF_1')
      | ~ v1_funct_1(C_37)
      | ~ v1_relat_1(C_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_34,c_80])).

tff(c_20,plain,(
    k1_funct_1(k5_relat_1('#skF_4','#skF_5'),'#skF_3') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_89,plain,
    ( ~ r2_hidden('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_20])).

tff(c_97,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_89])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:39:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.20  
% 1.96/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.20  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.96/1.20  
% 1.96/1.20  %Foreground sorts:
% 1.96/1.20  
% 1.96/1.20  
% 1.96/1.20  %Background operators:
% 1.96/1.20  
% 1.96/1.20  
% 1.96/1.20  %Foreground operators:
% 1.96/1.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.96/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.96/1.20  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.96/1.20  tff('#skF_5', type, '#skF_5': $i).
% 1.96/1.20  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.96/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.20  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.96/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.96/1.20  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.96/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.96/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.96/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.96/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.96/1.20  
% 2.07/1.21  tff(f_82, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_relat_1(E) & v1_funct_1(E)) => (r2_hidden(C, A) => ((B = k1_xboole_0) | (k1_funct_1(k5_relat_1(D, E), C) = k1_funct_1(E, k1_funct_1(D, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_2)).
% 2.07/1.21  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.07/1.21  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.07/1.21  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.07/1.21  tff(f_38, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 2.07/1.21  tff(c_28, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.07/1.21  tff(c_26, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.07/1.21  tff(c_24, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.07/1.21  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.07/1.21  tff(c_35, plain, (![C_15, A_16, B_17]: (v1_relat_1(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.07/1.21  tff(c_39, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_35])).
% 2.07/1.21  tff(c_34, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.07/1.21  tff(c_22, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.07/1.21  tff(c_32, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.07/1.21  tff(c_41, plain, (![A_19, B_20, C_21]: (k1_relset_1(A_19, B_20, C_21)=k1_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.07/1.21  tff(c_45, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_41])).
% 2.07/1.21  tff(c_53, plain, (![B_28, A_29, C_30]: (k1_xboole_0=B_28 | k1_relset_1(A_29, B_28, C_30)=A_29 | ~v1_funct_2(C_30, A_29, B_28) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_29, B_28))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.07/1.21  tff(c_56, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_53])).
% 2.07/1.21  tff(c_59, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_45, c_56])).
% 2.07/1.21  tff(c_60, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_22, c_59])).
% 2.07/1.21  tff(c_78, plain, (![B_34, C_35, A_36]: (k1_funct_1(k5_relat_1(B_34, C_35), A_36)=k1_funct_1(C_35, k1_funct_1(B_34, A_36)) | ~r2_hidden(A_36, k1_relat_1(B_34)) | ~v1_funct_1(C_35) | ~v1_relat_1(C_35) | ~v1_funct_1(B_34) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.07/1.21  tff(c_80, plain, (![C_35, A_36]: (k1_funct_1(k5_relat_1('#skF_4', C_35), A_36)=k1_funct_1(C_35, k1_funct_1('#skF_4', A_36)) | ~r2_hidden(A_36, '#skF_1') | ~v1_funct_1(C_35) | ~v1_relat_1(C_35) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_78])).
% 2.07/1.21  tff(c_83, plain, (![C_37, A_38]: (k1_funct_1(k5_relat_1('#skF_4', C_37), A_38)=k1_funct_1(C_37, k1_funct_1('#skF_4', A_38)) | ~r2_hidden(A_38, '#skF_1') | ~v1_funct_1(C_37) | ~v1_relat_1(C_37))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_34, c_80])).
% 2.07/1.21  tff(c_20, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_3')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.07/1.21  tff(c_89, plain, (~r2_hidden('#skF_3', '#skF_1') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_83, c_20])).
% 2.07/1.21  tff(c_97, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_89])).
% 2.07/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.21  
% 2.07/1.21  Inference rules
% 2.07/1.21  ----------------------
% 2.07/1.21  #Ref     : 0
% 2.07/1.21  #Sup     : 14
% 2.07/1.21  #Fact    : 0
% 2.07/1.21  #Define  : 0
% 2.07/1.21  #Split   : 0
% 2.07/1.21  #Chain   : 0
% 2.07/1.21  #Close   : 0
% 2.07/1.21  
% 2.07/1.21  Ordering : KBO
% 2.07/1.21  
% 2.07/1.21  Simplification rules
% 2.07/1.21  ----------------------
% 2.07/1.21  #Subsume      : 0
% 2.07/1.21  #Demod        : 10
% 2.07/1.21  #Tautology    : 8
% 2.07/1.21  #SimpNegUnit  : 2
% 2.07/1.21  #BackRed      : 1
% 2.07/1.21  
% 2.07/1.21  #Partial instantiations: 0
% 2.07/1.21  #Strategies tried      : 1
% 2.07/1.21  
% 2.07/1.21  Timing (in seconds)
% 2.07/1.21  ----------------------
% 2.07/1.21  Preprocessing        : 0.32
% 2.07/1.21  Parsing              : 0.17
% 2.07/1.21  CNF conversion       : 0.02
% 2.07/1.21  Main loop            : 0.13
% 2.07/1.21  Inferencing          : 0.05
% 2.07/1.21  Reduction            : 0.04
% 2.07/1.21  Demodulation         : 0.03
% 2.07/1.21  BG Simplification    : 0.01
% 2.07/1.21  Subsumption          : 0.02
% 2.07/1.21  Abstraction          : 0.01
% 2.07/1.21  MUC search           : 0.00
% 2.07/1.21  Cooper               : 0.00
% 2.07/1.21  Total                : 0.48
% 2.07/1.21  Index Insertion      : 0.00
% 2.07/1.21  Index Deletion       : 0.00
% 2.07/1.21  Index Matching       : 0.00
% 2.07/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------

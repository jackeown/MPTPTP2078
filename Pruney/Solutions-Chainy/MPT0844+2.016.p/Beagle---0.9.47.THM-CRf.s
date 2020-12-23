%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:42 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   53 (  73 expanded)
%              Number of leaves         :   26 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :   74 ( 114 expanded)
%              Number of equality atoms :   18 (  32 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_xboole_0(B,C)
         => k5_relset_1(C,A,D,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( r1_tarski(B,C)
       => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_70,plain,(
    ! [A_41,B_42,C_43,D_44] :
      ( k5_relset_1(A_41,B_42,C_43,D_44) = k7_relat_1(C_43,D_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_73,plain,(
    ! [D_44] : k5_relset_1('#skF_3','#skF_1','#skF_4',D_44) = k7_relat_1('#skF_4',D_44) ),
    inference(resolution,[status(thm)],[c_28,c_70])).

tff(c_24,plain,(
    k5_relset_1('#skF_3','#skF_1','#skF_4','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_74,plain,(
    k7_relat_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_24])).

tff(c_26,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_31,plain,(
    ! [B_28,A_29] :
      ( r1_xboole_0(B_28,A_29)
      | ~ r1_xboole_0(A_29,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_34,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_31])).

tff(c_35,plain,(
    ! [C_30,A_31,B_32] :
      ( v1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_39,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_35])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_84,plain,(
    ! [A_46,C_47,D_48,B_49] :
      ( m1_subset_1(k5_relset_1(A_46,C_47,D_48,B_49),k1_zfmisc_1(k2_zfmisc_1(B_49,C_47)))
      | ~ m1_subset_1(D_48,k1_zfmisc_1(k2_zfmisc_1(A_46,C_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_94,plain,(
    ! [D_44] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_44),k1_zfmisc_1(k2_zfmisc_1(D_44,'#skF_1')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_84])).

tff(c_99,plain,(
    ! [D_44] : m1_subset_1(k7_relat_1('#skF_4',D_44),k1_zfmisc_1(k2_zfmisc_1(D_44,'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_94])).

tff(c_157,plain,(
    ! [B_59,A_60,D_61,C_62] :
      ( r2_relset_1(B_59,A_60,k5_relset_1(B_59,A_60,D_61,C_62),D_61)
      | ~ r1_tarski(B_59,C_62)
      | ~ m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(B_59,A_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_165,plain,(
    ! [C_62] :
      ( r2_relset_1('#skF_3','#skF_1',k5_relset_1('#skF_3','#skF_1','#skF_4',C_62),'#skF_4')
      | ~ r1_tarski('#skF_3',C_62) ) ),
    inference(resolution,[status(thm)],[c_28,c_157])).

tff(c_283,plain,(
    ! [C_74] :
      ( r2_relset_1('#skF_3','#skF_1',k7_relat_1('#skF_4',C_74),'#skF_4')
      | ~ r1_tarski('#skF_3',C_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_165])).

tff(c_18,plain,(
    ! [D_18,C_17,A_15,B_16] :
      ( D_18 = C_17
      | ~ r2_relset_1(A_15,B_16,C_17,D_18)
      | ~ m1_subset_1(D_18,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16)))
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_285,plain,(
    ! [C_74] :
      ( k7_relat_1('#skF_4',C_74) = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ m1_subset_1(k7_relat_1('#skF_4',C_74),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ r1_tarski('#skF_3',C_74) ) ),
    inference(resolution,[status(thm)],[c_283,c_18])).

tff(c_544,plain,(
    ! [C_106] :
      ( k7_relat_1('#skF_4',C_106) = '#skF_4'
      | ~ m1_subset_1(k7_relat_1('#skF_4',C_106),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ r1_tarski('#skF_3',C_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_285])).

tff(c_548,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_99,c_544])).

tff(c_551,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_548])).

tff(c_10,plain,(
    ! [C_7,A_5,B_6] :
      ( k7_relat_1(k7_relat_1(C_7,A_5),B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6)
      | ~ v1_relat_1(C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_581,plain,(
    ! [B_6] :
      ( k7_relat_1('#skF_4',B_6) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_6)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_551,c_10])).

tff(c_599,plain,(
    ! [B_107] :
      ( k7_relat_1('#skF_4',B_107) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_581])).

tff(c_602,plain,(
    k7_relat_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_599])).

tff(c_606,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_602])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:10:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.41  
% 2.63/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.41  %$ r2_relset_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.63/1.41  
% 2.63/1.41  %Foreground sorts:
% 2.63/1.41  
% 2.63/1.41  
% 2.63/1.41  %Background operators:
% 2.63/1.41  
% 2.63/1.41  
% 2.63/1.41  %Foreground operators:
% 2.63/1.41  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.63/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.41  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.63/1.41  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.63/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.63/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.63/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.63/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.63/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.63/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.63/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.63/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.63/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.63/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.63/1.41  
% 2.63/1.43  tff(f_74, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_xboole_0(B, C) => (k5_relset_1(C, A, D, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relset_1)).
% 2.63/1.43  tff(f_49, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.63/1.43  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.63/1.43  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.63/1.43  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.63/1.43  tff(f_61, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_relset_1)).
% 2.63/1.43  tff(f_67, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relset_1)).
% 2.63/1.43  tff(f_57, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.63/1.43  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 2.63/1.43  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.63/1.43  tff(c_70, plain, (![A_41, B_42, C_43, D_44]: (k5_relset_1(A_41, B_42, C_43, D_44)=k7_relat_1(C_43, D_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.63/1.43  tff(c_73, plain, (![D_44]: (k5_relset_1('#skF_3', '#skF_1', '#skF_4', D_44)=k7_relat_1('#skF_4', D_44))), inference(resolution, [status(thm)], [c_28, c_70])).
% 2.63/1.43  tff(c_24, plain, (k5_relset_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.63/1.43  tff(c_74, plain, (k7_relat_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_73, c_24])).
% 2.63/1.43  tff(c_26, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.63/1.43  tff(c_31, plain, (![B_28, A_29]: (r1_xboole_0(B_28, A_29) | ~r1_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.63/1.43  tff(c_34, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_31])).
% 2.63/1.43  tff(c_35, plain, (![C_30, A_31, B_32]: (v1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.63/1.43  tff(c_39, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_35])).
% 2.63/1.43  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.63/1.43  tff(c_84, plain, (![A_46, C_47, D_48, B_49]: (m1_subset_1(k5_relset_1(A_46, C_47, D_48, B_49), k1_zfmisc_1(k2_zfmisc_1(B_49, C_47))) | ~m1_subset_1(D_48, k1_zfmisc_1(k2_zfmisc_1(A_46, C_47))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.63/1.43  tff(c_94, plain, (![D_44]: (m1_subset_1(k7_relat_1('#skF_4', D_44), k1_zfmisc_1(k2_zfmisc_1(D_44, '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_73, c_84])).
% 2.63/1.43  tff(c_99, plain, (![D_44]: (m1_subset_1(k7_relat_1('#skF_4', D_44), k1_zfmisc_1(k2_zfmisc_1(D_44, '#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_94])).
% 2.63/1.43  tff(c_157, plain, (![B_59, A_60, D_61, C_62]: (r2_relset_1(B_59, A_60, k5_relset_1(B_59, A_60, D_61, C_62), D_61) | ~r1_tarski(B_59, C_62) | ~m1_subset_1(D_61, k1_zfmisc_1(k2_zfmisc_1(B_59, A_60))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.63/1.43  tff(c_165, plain, (![C_62]: (r2_relset_1('#skF_3', '#skF_1', k5_relset_1('#skF_3', '#skF_1', '#skF_4', C_62), '#skF_4') | ~r1_tarski('#skF_3', C_62))), inference(resolution, [status(thm)], [c_28, c_157])).
% 2.63/1.43  tff(c_283, plain, (![C_74]: (r2_relset_1('#skF_3', '#skF_1', k7_relat_1('#skF_4', C_74), '#skF_4') | ~r1_tarski('#skF_3', C_74))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_165])).
% 2.63/1.43  tff(c_18, plain, (![D_18, C_17, A_15, B_16]: (D_18=C_17 | ~r2_relset_1(A_15, B_16, C_17, D_18) | ~m1_subset_1(D_18, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.63/1.43  tff(c_285, plain, (![C_74]: (k7_relat_1('#skF_4', C_74)='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~m1_subset_1(k7_relat_1('#skF_4', C_74), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~r1_tarski('#skF_3', C_74))), inference(resolution, [status(thm)], [c_283, c_18])).
% 2.63/1.43  tff(c_544, plain, (![C_106]: (k7_relat_1('#skF_4', C_106)='#skF_4' | ~m1_subset_1(k7_relat_1('#skF_4', C_106), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~r1_tarski('#skF_3', C_106))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_285])).
% 2.63/1.43  tff(c_548, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_99, c_544])).
% 2.63/1.43  tff(c_551, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_548])).
% 2.63/1.43  tff(c_10, plain, (![C_7, A_5, B_6]: (k7_relat_1(k7_relat_1(C_7, A_5), B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6) | ~v1_relat_1(C_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.63/1.43  tff(c_581, plain, (![B_6]: (k7_relat_1('#skF_4', B_6)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_6) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_551, c_10])).
% 2.63/1.43  tff(c_599, plain, (![B_107]: (k7_relat_1('#skF_4', B_107)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_107))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_581])).
% 2.63/1.43  tff(c_602, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_599])).
% 2.63/1.43  tff(c_606, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_602])).
% 2.63/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.43  
% 2.63/1.43  Inference rules
% 2.63/1.43  ----------------------
% 2.63/1.43  #Ref     : 0
% 2.63/1.43  #Sup     : 130
% 2.63/1.43  #Fact    : 0
% 2.63/1.43  #Define  : 0
% 2.63/1.43  #Split   : 2
% 2.63/1.43  #Chain   : 0
% 2.63/1.43  #Close   : 0
% 2.63/1.43  
% 2.63/1.43  Ordering : KBO
% 2.63/1.43  
% 2.63/1.43  Simplification rules
% 2.63/1.43  ----------------------
% 2.63/1.43  #Subsume      : 6
% 2.63/1.43  #Demod        : 103
% 2.63/1.43  #Tautology    : 69
% 2.63/1.43  #SimpNegUnit  : 5
% 2.63/1.43  #BackRed      : 5
% 2.63/1.43  
% 2.63/1.43  #Partial instantiations: 0
% 2.63/1.43  #Strategies tried      : 1
% 2.63/1.43  
% 2.63/1.43  Timing (in seconds)
% 2.63/1.43  ----------------------
% 2.63/1.43  Preprocessing        : 0.32
% 2.63/1.43  Parsing              : 0.18
% 2.63/1.43  CNF conversion       : 0.02
% 2.63/1.43  Main loop            : 0.30
% 2.63/1.43  Inferencing          : 0.11
% 2.63/1.43  Reduction            : 0.10
% 2.63/1.43  Demodulation         : 0.08
% 2.63/1.43  BG Simplification    : 0.01
% 2.76/1.43  Subsumption          : 0.05
% 2.76/1.43  Abstraction          : 0.02
% 2.76/1.43  MUC search           : 0.00
% 2.76/1.43  Cooper               : 0.00
% 2.76/1.43  Total                : 0.65
% 2.76/1.43  Index Insertion      : 0.00
% 2.76/1.43  Index Deletion       : 0.00
% 2.76/1.43  Index Matching       : 0.00
% 2.76/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------

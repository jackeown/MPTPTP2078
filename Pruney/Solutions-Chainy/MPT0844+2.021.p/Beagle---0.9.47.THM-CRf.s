%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:42 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   53 (  68 expanded)
%              Number of leaves         :   27 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   63 (  94 expanded)
%              Number of equality atoms :   24 (  30 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_xboole_0(B,C)
         => k5_relset_1(C,A,D,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_24,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_61,plain,(
    ! [A_26,B_27] :
      ( k3_xboole_0(A_26,B_27) = k1_xboole_0
      | ~ r1_xboole_0(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_61])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_69,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_2])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_94,plain,(
    ! [B_30,A_31] :
      ( v1_relat_1(B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_31))
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_97,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_94])).

tff(c_100,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_97])).

tff(c_107,plain,(
    ! [C_37,A_38,B_39] :
      ( v4_relat_1(C_37,A_38)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_111,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_107])).

tff(c_14,plain,(
    ! [B_14,A_13] :
      ( k7_relat_1(B_14,A_13) = B_14
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_114,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_111,c_14])).

tff(c_117,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_114])).

tff(c_122,plain,(
    ! [C_40,A_41,B_42] :
      ( k7_relat_1(k7_relat_1(C_40,A_41),B_42) = k1_xboole_0
      | ~ r1_xboole_0(A_41,B_42)
      | ~ v1_relat_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_137,plain,(
    ! [B_42] :
      ( k7_relat_1('#skF_4',B_42) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_42)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_122])).

tff(c_142,plain,(
    ! [B_43] :
      ( k7_relat_1('#skF_4',B_43) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_137])).

tff(c_147,plain,(
    ! [B_4] :
      ( k7_relat_1('#skF_4',B_4) = k1_xboole_0
      | k3_xboole_0('#skF_3',B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_142])).

tff(c_169,plain,(
    ! [A_45,B_46,C_47,D_48] :
      ( k5_relset_1(A_45,B_46,C_47,D_48) = k7_relat_1(C_47,D_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_172,plain,(
    ! [D_48] : k5_relset_1('#skF_3','#skF_1','#skF_4',D_48) = k7_relat_1('#skF_4',D_48) ),
    inference(resolution,[status(thm)],[c_26,c_169])).

tff(c_22,plain,(
    k5_relset_1('#skF_3','#skF_1','#skF_4','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_173,plain,(
    k7_relat_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_22])).

tff(c_185,plain,(
    k3_xboole_0('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_173])).

tff(c_189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_185])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:39:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.21  
% 1.90/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.21  %$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.90/1.21  
% 1.90/1.21  %Foreground sorts:
% 1.90/1.21  
% 1.90/1.21  
% 1.90/1.21  %Background operators:
% 1.90/1.21  
% 1.90/1.21  
% 1.90/1.21  %Foreground operators:
% 1.90/1.21  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 1.90/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.21  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.90/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.90/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.90/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.90/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.90/1.21  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.90/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.90/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.90/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.90/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.90/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.21  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.90/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.90/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.90/1.21  
% 1.90/1.23  tff(f_69, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_xboole_0(B, C) => (k5_relset_1(C, A, D, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relset_1)).
% 1.90/1.23  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.90/1.23  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.90/1.23  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.90/1.23  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.90/1.23  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.90/1.23  tff(f_52, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 1.90/1.23  tff(f_46, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 1.90/1.23  tff(f_62, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 1.90/1.23  tff(c_24, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.90/1.23  tff(c_61, plain, (![A_26, B_27]: (k3_xboole_0(A_26, B_27)=k1_xboole_0 | ~r1_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.90/1.23  tff(c_65, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_61])).
% 1.90/1.23  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.90/1.23  tff(c_69, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_65, c_2])).
% 1.90/1.23  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.90/1.23  tff(c_10, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.90/1.23  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.90/1.23  tff(c_94, plain, (![B_30, A_31]: (v1_relat_1(B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(A_31)) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.90/1.23  tff(c_97, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_26, c_94])).
% 1.90/1.23  tff(c_100, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_97])).
% 1.90/1.23  tff(c_107, plain, (![C_37, A_38, B_39]: (v4_relat_1(C_37, A_38) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.90/1.23  tff(c_111, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_107])).
% 1.90/1.23  tff(c_14, plain, (![B_14, A_13]: (k7_relat_1(B_14, A_13)=B_14 | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.90/1.23  tff(c_114, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_111, c_14])).
% 1.90/1.23  tff(c_117, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_114])).
% 1.90/1.23  tff(c_122, plain, (![C_40, A_41, B_42]: (k7_relat_1(k7_relat_1(C_40, A_41), B_42)=k1_xboole_0 | ~r1_xboole_0(A_41, B_42) | ~v1_relat_1(C_40))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.90/1.23  tff(c_137, plain, (![B_42]: (k7_relat_1('#skF_4', B_42)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_42) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_117, c_122])).
% 1.90/1.23  tff(c_142, plain, (![B_43]: (k7_relat_1('#skF_4', B_43)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_43))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_137])).
% 1.90/1.23  tff(c_147, plain, (![B_4]: (k7_relat_1('#skF_4', B_4)=k1_xboole_0 | k3_xboole_0('#skF_3', B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_142])).
% 1.90/1.23  tff(c_169, plain, (![A_45, B_46, C_47, D_48]: (k5_relset_1(A_45, B_46, C_47, D_48)=k7_relat_1(C_47, D_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.90/1.23  tff(c_172, plain, (![D_48]: (k5_relset_1('#skF_3', '#skF_1', '#skF_4', D_48)=k7_relat_1('#skF_4', D_48))), inference(resolution, [status(thm)], [c_26, c_169])).
% 1.90/1.23  tff(c_22, plain, (k5_relset_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.90/1.23  tff(c_173, plain, (k7_relat_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_172, c_22])).
% 1.90/1.23  tff(c_185, plain, (k3_xboole_0('#skF_3', '#skF_2')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_147, c_173])).
% 1.90/1.23  tff(c_189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_185])).
% 1.90/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.23  
% 1.90/1.23  Inference rules
% 1.90/1.23  ----------------------
% 1.90/1.23  #Ref     : 0
% 1.90/1.23  #Sup     : 39
% 1.90/1.23  #Fact    : 0
% 1.90/1.23  #Define  : 0
% 1.90/1.23  #Split   : 1
% 1.90/1.23  #Chain   : 0
% 1.90/1.23  #Close   : 0
% 1.90/1.23  
% 1.90/1.23  Ordering : KBO
% 1.90/1.23  
% 1.90/1.23  Simplification rules
% 1.90/1.23  ----------------------
% 1.90/1.23  #Subsume      : 1
% 1.90/1.23  #Demod        : 9
% 1.90/1.23  #Tautology    : 24
% 1.90/1.23  #SimpNegUnit  : 0
% 1.90/1.23  #BackRed      : 1
% 1.90/1.23  
% 1.90/1.23  #Partial instantiations: 0
% 1.90/1.23  #Strategies tried      : 1
% 1.90/1.23  
% 1.90/1.23  Timing (in seconds)
% 1.90/1.23  ----------------------
% 1.90/1.23  Preprocessing        : 0.30
% 1.90/1.23  Parsing              : 0.16
% 1.90/1.23  CNF conversion       : 0.02
% 1.90/1.23  Main loop            : 0.16
% 1.90/1.23  Inferencing          : 0.06
% 1.90/1.23  Reduction            : 0.05
% 1.90/1.23  Demodulation         : 0.04
% 1.90/1.23  BG Simplification    : 0.01
% 1.90/1.23  Subsumption          : 0.03
% 2.05/1.23  Abstraction          : 0.01
% 2.05/1.23  MUC search           : 0.00
% 2.05/1.23  Cooper               : 0.00
% 2.05/1.23  Total                : 0.50
% 2.05/1.23  Index Insertion      : 0.00
% 2.05/1.23  Index Deletion       : 0.00
% 2.05/1.23  Index Matching       : 0.00
% 2.05/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------

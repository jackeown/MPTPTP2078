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
% DateTime   : Thu Dec  3 10:08:41 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   47 (  70 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :   55 ( 100 expanded)
%              Number of equality atoms :   15 (  28 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_xboole_0(B,C)
         => k5_relset_1(C,A,D,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k5_relset_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(c_20,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_68,plain,(
    ! [A_35,B_36,C_37,D_38] :
      ( k5_relset_1(A_35,B_36,C_37,D_38) = k7_relat_1(C_37,D_38)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_71,plain,(
    ! [D_38] : k5_relset_1('#skF_3','#skF_1','#skF_4',D_38) = k7_relat_1('#skF_4',D_38) ),
    inference(resolution,[status(thm)],[c_20,c_68])).

tff(c_16,plain,(
    k5_relset_1('#skF_3','#skF_1','#skF_4','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_72,plain,(
    k7_relat_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_16])).

tff(c_18,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_21,plain,(
    ! [C_20,A_21,B_22] :
      ( v1_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_25,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_21])).

tff(c_82,plain,(
    ! [A_40,B_41,C_42,D_43] :
      ( m1_subset_1(k5_relset_1(A_40,B_41,C_42,D_43),k1_zfmisc_1(k2_zfmisc_1(A_40,B_41)))
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_96,plain,(
    ! [D_38] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_38),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_82])).

tff(c_103,plain,(
    ! [D_44] : m1_subset_1(k7_relat_1('#skF_4',D_44),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_96])).

tff(c_6,plain,(
    ! [C_8,A_6,B_7] :
      ( v1_relat_1(C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_120,plain,(
    ! [D_44] : v1_relat_1(k7_relat_1('#skF_4',D_44)) ),
    inference(resolution,[status(thm)],[c_103,c_6])).

tff(c_10,plain,(
    ! [C_11,A_9,B_10] :
      ( v4_relat_1(C_11,A_9)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_130,plain,(
    ! [D_47] : v4_relat_1(k7_relat_1('#skF_4',D_47),'#skF_3') ),
    inference(resolution,[status(thm)],[c_103,c_10])).

tff(c_4,plain,(
    ! [B_5,A_4] :
      ( k7_relat_1(B_5,A_4) = B_5
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_133,plain,(
    ! [D_47] :
      ( k7_relat_1(k7_relat_1('#skF_4',D_47),'#skF_3') = k7_relat_1('#skF_4',D_47)
      | ~ v1_relat_1(k7_relat_1('#skF_4',D_47)) ) ),
    inference(resolution,[status(thm)],[c_130,c_4])).

tff(c_140,plain,(
    ! [D_48] : k7_relat_1(k7_relat_1('#skF_4',D_48),'#skF_3') = k7_relat_1('#skF_4',D_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_133])).

tff(c_2,plain,(
    ! [C_3,A_1,B_2] :
      ( k7_relat_1(k7_relat_1(C_3,A_1),B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2)
      | ~ v1_relat_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_149,plain,(
    ! [D_48] :
      ( k7_relat_1('#skF_4',D_48) = k1_xboole_0
      | ~ r1_xboole_0(D_48,'#skF_3')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_2])).

tff(c_169,plain,(
    ! [D_49] :
      ( k7_relat_1('#skF_4',D_49) = k1_xboole_0
      | ~ r1_xboole_0(D_49,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_149])).

tff(c_172,plain,(
    k7_relat_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_169])).

tff(c_176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:41:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.20  
% 1.92/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.20  %$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.92/1.20  
% 1.92/1.20  %Foreground sorts:
% 1.92/1.20  
% 1.92/1.20  
% 1.92/1.20  %Background operators:
% 1.92/1.20  
% 1.92/1.20  
% 1.92/1.20  %Foreground operators:
% 1.92/1.20  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 1.92/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.20  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.92/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.92/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.92/1.20  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.92/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.92/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.92/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.92/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.92/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.20  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.92/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.92/1.20  
% 1.92/1.21  tff(f_62, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_xboole_0(B, C) => (k5_relset_1(C, A, D, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relset_1)).
% 1.92/1.21  tff(f_55, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 1.92/1.21  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.92/1.21  tff(f_51, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k5_relset_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relset_1)).
% 1.92/1.21  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.92/1.21  tff(f_37, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 1.92/1.21  tff(f_31, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 1.92/1.21  tff(c_20, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.92/1.21  tff(c_68, plain, (![A_35, B_36, C_37, D_38]: (k5_relset_1(A_35, B_36, C_37, D_38)=k7_relat_1(C_37, D_38) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.92/1.21  tff(c_71, plain, (![D_38]: (k5_relset_1('#skF_3', '#skF_1', '#skF_4', D_38)=k7_relat_1('#skF_4', D_38))), inference(resolution, [status(thm)], [c_20, c_68])).
% 1.92/1.21  tff(c_16, plain, (k5_relset_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.92/1.21  tff(c_72, plain, (k7_relat_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_71, c_16])).
% 1.92/1.21  tff(c_18, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.92/1.21  tff(c_21, plain, (![C_20, A_21, B_22]: (v1_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.92/1.21  tff(c_25, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_21])).
% 1.92/1.21  tff(c_82, plain, (![A_40, B_41, C_42, D_43]: (m1_subset_1(k5_relset_1(A_40, B_41, C_42, D_43), k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.92/1.21  tff(c_96, plain, (![D_38]: (m1_subset_1(k7_relat_1('#skF_4', D_38), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_71, c_82])).
% 1.92/1.21  tff(c_103, plain, (![D_44]: (m1_subset_1(k7_relat_1('#skF_4', D_44), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_96])).
% 1.92/1.21  tff(c_6, plain, (![C_8, A_6, B_7]: (v1_relat_1(C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.92/1.21  tff(c_120, plain, (![D_44]: (v1_relat_1(k7_relat_1('#skF_4', D_44)))), inference(resolution, [status(thm)], [c_103, c_6])).
% 1.92/1.21  tff(c_10, plain, (![C_11, A_9, B_10]: (v4_relat_1(C_11, A_9) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.92/1.21  tff(c_130, plain, (![D_47]: (v4_relat_1(k7_relat_1('#skF_4', D_47), '#skF_3'))), inference(resolution, [status(thm)], [c_103, c_10])).
% 1.92/1.21  tff(c_4, plain, (![B_5, A_4]: (k7_relat_1(B_5, A_4)=B_5 | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.92/1.21  tff(c_133, plain, (![D_47]: (k7_relat_1(k7_relat_1('#skF_4', D_47), '#skF_3')=k7_relat_1('#skF_4', D_47) | ~v1_relat_1(k7_relat_1('#skF_4', D_47)))), inference(resolution, [status(thm)], [c_130, c_4])).
% 1.92/1.21  tff(c_140, plain, (![D_48]: (k7_relat_1(k7_relat_1('#skF_4', D_48), '#skF_3')=k7_relat_1('#skF_4', D_48))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_133])).
% 1.92/1.21  tff(c_2, plain, (![C_3, A_1, B_2]: (k7_relat_1(k7_relat_1(C_3, A_1), B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2) | ~v1_relat_1(C_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.92/1.21  tff(c_149, plain, (![D_48]: (k7_relat_1('#skF_4', D_48)=k1_xboole_0 | ~r1_xboole_0(D_48, '#skF_3') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_140, c_2])).
% 1.92/1.21  tff(c_169, plain, (![D_49]: (k7_relat_1('#skF_4', D_49)=k1_xboole_0 | ~r1_xboole_0(D_49, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_25, c_149])).
% 1.92/1.21  tff(c_172, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_169])).
% 1.92/1.21  tff(c_176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_172])).
% 1.92/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.21  
% 1.92/1.21  Inference rules
% 1.92/1.21  ----------------------
% 1.92/1.21  #Ref     : 0
% 1.92/1.21  #Sup     : 35
% 1.92/1.21  #Fact    : 0
% 1.92/1.21  #Define  : 0
% 1.92/1.21  #Split   : 0
% 1.92/1.21  #Chain   : 0
% 1.92/1.21  #Close   : 0
% 1.92/1.21  
% 1.92/1.21  Ordering : KBO
% 1.92/1.21  
% 1.92/1.21  Simplification rules
% 1.92/1.21  ----------------------
% 1.92/1.21  #Subsume      : 0
% 1.92/1.21  #Demod        : 14
% 1.92/1.21  #Tautology    : 13
% 1.92/1.21  #SimpNegUnit  : 1
% 1.92/1.21  #BackRed      : 1
% 1.92/1.21  
% 1.92/1.21  #Partial instantiations: 0
% 1.92/1.21  #Strategies tried      : 1
% 1.92/1.21  
% 1.92/1.21  Timing (in seconds)
% 1.92/1.21  ----------------------
% 1.92/1.21  Preprocessing        : 0.29
% 1.92/1.21  Parsing              : 0.16
% 1.92/1.21  CNF conversion       : 0.02
% 1.92/1.21  Main loop            : 0.15
% 1.92/1.21  Inferencing          : 0.06
% 1.92/1.21  Reduction            : 0.04
% 1.92/1.21  Demodulation         : 0.03
% 1.92/1.21  BG Simplification    : 0.01
% 1.92/1.21  Subsumption          : 0.02
% 1.92/1.22  Abstraction          : 0.01
% 1.92/1.22  MUC search           : 0.00
% 1.92/1.22  Cooper               : 0.00
% 1.92/1.22  Total                : 0.47
% 1.92/1.22  Index Insertion      : 0.00
% 1.92/1.22  Index Deletion       : 0.00
% 1.92/1.22  Index Matching       : 0.00
% 1.92/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------

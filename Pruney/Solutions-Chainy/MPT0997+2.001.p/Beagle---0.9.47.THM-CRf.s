%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:52 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   46 (  58 expanded)
%              Number of leaves         :   27 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 (  87 expanded)
%              Number of equality atoms :   20 (  35 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_funct_2)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,(
    ! [C_18,A_19,B_20] :
      ( v1_relat_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_30,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_26])).

tff(c_37,plain,(
    ! [C_26,A_27,B_28] :
      ( v4_relat_1(C_26,A_27)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_41,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_37])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( k7_relat_1(B_4,A_3) = B_4
      | ~ v4_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_44,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_41,c_4])).

tff(c_47,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_44])).

tff(c_52,plain,(
    ! [B_29,A_30] :
      ( k2_relat_1(k7_relat_1(B_29,A_30)) = k9_relat_1(B_29,A_30)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_61,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_52])).

tff(c_65,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_61])).

tff(c_80,plain,(
    ! [A_34,B_35,C_36,D_37] :
      ( k7_relset_1(A_34,B_35,C_36,D_37) = k9_relat_1(C_36,D_37)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_83,plain,(
    ! [D_37] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_37) = k9_relat_1('#skF_3',D_37) ),
    inference(resolution,[status(thm)],[c_20,c_80])).

tff(c_66,plain,(
    ! [A_31,B_32,C_33] :
      ( k2_relset_1(A_31,B_32,C_33) = k2_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_70,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_66])).

tff(c_16,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_75,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_16])).

tff(c_84,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_75])).

tff(c_87,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_84])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:55:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.14  
% 1.79/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.14  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.79/1.14  
% 1.79/1.14  %Foreground sorts:
% 1.79/1.14  
% 1.79/1.14  
% 1.79/1.14  %Background operators:
% 1.79/1.14  
% 1.79/1.14  
% 1.79/1.14  %Foreground operators:
% 1.79/1.14  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.79/1.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.79/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.14  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.79/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.79/1.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.79/1.14  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.79/1.14  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.79/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.14  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.79/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.79/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.79/1.14  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.79/1.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.79/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.79/1.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.79/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.14  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.79/1.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.79/1.14  
% 1.79/1.15  tff(f_66, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_funct_2)).
% 1.79/1.15  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.79/1.15  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.79/1.15  tff(f_35, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 1.79/1.15  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.79/1.15  tff(f_53, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 1.79/1.15  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 1.79/1.15  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.79/1.15  tff(c_26, plain, (![C_18, A_19, B_20]: (v1_relat_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.79/1.15  tff(c_30, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_26])).
% 1.79/1.15  tff(c_37, plain, (![C_26, A_27, B_28]: (v4_relat_1(C_26, A_27) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.79/1.15  tff(c_41, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_20, c_37])).
% 1.79/1.15  tff(c_4, plain, (![B_4, A_3]: (k7_relat_1(B_4, A_3)=B_4 | ~v4_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.79/1.15  tff(c_44, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_41, c_4])).
% 1.79/1.15  tff(c_47, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_44])).
% 1.79/1.15  tff(c_52, plain, (![B_29, A_30]: (k2_relat_1(k7_relat_1(B_29, A_30))=k9_relat_1(B_29, A_30) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.79/1.15  tff(c_61, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_47, c_52])).
% 1.79/1.15  tff(c_65, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_61])).
% 1.79/1.15  tff(c_80, plain, (![A_34, B_35, C_36, D_37]: (k7_relset_1(A_34, B_35, C_36, D_37)=k9_relat_1(C_36, D_37) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.79/1.15  tff(c_83, plain, (![D_37]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_37)=k9_relat_1('#skF_3', D_37))), inference(resolution, [status(thm)], [c_20, c_80])).
% 1.79/1.15  tff(c_66, plain, (![A_31, B_32, C_33]: (k2_relset_1(A_31, B_32, C_33)=k2_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.79/1.15  tff(c_70, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_66])).
% 1.79/1.15  tff(c_16, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.79/1.15  tff(c_75, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_16])).
% 1.79/1.15  tff(c_84, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_75])).
% 1.79/1.15  tff(c_87, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_84])).
% 1.79/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.15  
% 1.79/1.15  Inference rules
% 1.79/1.15  ----------------------
% 1.79/1.15  #Ref     : 0
% 1.79/1.15  #Sup     : 15
% 1.79/1.15  #Fact    : 0
% 1.79/1.15  #Define  : 0
% 1.79/1.15  #Split   : 1
% 1.79/1.15  #Chain   : 0
% 1.79/1.15  #Close   : 0
% 1.79/1.15  
% 1.79/1.15  Ordering : KBO
% 1.79/1.15  
% 1.79/1.15  Simplification rules
% 1.79/1.15  ----------------------
% 1.79/1.15  #Subsume      : 0
% 1.79/1.15  #Demod        : 5
% 1.79/1.15  #Tautology    : 8
% 1.79/1.15  #SimpNegUnit  : 0
% 1.79/1.15  #BackRed      : 2
% 1.79/1.15  
% 1.79/1.15  #Partial instantiations: 0
% 1.79/1.15  #Strategies tried      : 1
% 1.79/1.15  
% 1.79/1.15  Timing (in seconds)
% 1.79/1.15  ----------------------
% 1.79/1.16  Preprocessing        : 0.30
% 1.79/1.16  Parsing              : 0.17
% 1.79/1.16  CNF conversion       : 0.02
% 1.79/1.16  Main loop            : 0.10
% 1.79/1.16  Inferencing          : 0.04
% 1.79/1.16  Reduction            : 0.03
% 1.79/1.16  Demodulation         : 0.02
% 1.79/1.16  BG Simplification    : 0.01
% 1.79/1.16  Subsumption          : 0.01
% 1.79/1.16  Abstraction          : 0.00
% 1.79/1.16  MUC search           : 0.00
% 1.79/1.16  Cooper               : 0.00
% 1.79/1.16  Total                : 0.42
% 1.79/1.16  Index Insertion      : 0.00
% 1.79/1.16  Index Deletion       : 0.00
% 1.79/1.16  Index Matching       : 0.00
% 1.79/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------

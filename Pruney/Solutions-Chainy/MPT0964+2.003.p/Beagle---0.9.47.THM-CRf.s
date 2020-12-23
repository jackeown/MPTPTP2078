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
% DateTime   : Thu Dec  3 10:10:59 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   48 (  59 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   61 ( 112 expanded)
%              Number of equality atoms :   21 (  29 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_63,axiom,(
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

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_26,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_30,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_48,plain,(
    ! [A_21,B_22,C_23] :
      ( k1_relset_1(A_21,B_22,C_23) = k1_relat_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_52,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_48])).

tff(c_75,plain,(
    ! [B_36,A_37,C_38] :
      ( k1_xboole_0 = B_36
      | k1_relset_1(A_37,B_36,C_38) = A_37
      | ~ v1_funct_2(C_38,A_37,B_36)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_37,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_78,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_75])).

tff(c_81,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_52,c_78])).

tff(c_82,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_81])).

tff(c_33,plain,(
    ! [C_15,A_16,B_17] :
      ( v1_relat_1(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_37,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_33])).

tff(c_32,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_58,plain,(
    ! [B_25,A_26] :
      ( r2_hidden(k1_funct_1(B_25,A_26),k2_relat_1(B_25))
      | ~ r2_hidden(A_26,k1_relat_1(B_25))
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    ! [A_18,B_19,C_20] :
      ( k2_relset_1(A_18,B_19,C_20) = k2_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_42,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_38])).

tff(c_22,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_3'),k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_43,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_22])).

tff(c_61,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_43])).

tff(c_64,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_32,c_61])).

tff(c_83,plain,(
    ~ r2_hidden('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_64])).

tff(c_87,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_83])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:15:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.16  
% 1.69/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.16  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.69/1.16  
% 1.69/1.16  %Foreground sorts:
% 1.69/1.16  
% 1.69/1.16  
% 1.69/1.16  %Background operators:
% 1.69/1.16  
% 1.69/1.16  
% 1.69/1.16  %Foreground operators:
% 1.69/1.16  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.69/1.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.69/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.69/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.69/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.69/1.16  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.69/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.69/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.69/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.16  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.69/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.69/1.16  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.69/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.69/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.69/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.69/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.69/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.69/1.16  
% 1.90/1.17  tff(f_76, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 1.90/1.17  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.90/1.17  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 1.90/1.17  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.90/1.17  tff(f_33, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 1.90/1.17  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 1.90/1.17  tff(c_26, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.90/1.17  tff(c_24, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.90/1.17  tff(c_30, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.90/1.17  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.90/1.17  tff(c_48, plain, (![A_21, B_22, C_23]: (k1_relset_1(A_21, B_22, C_23)=k1_relat_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.90/1.17  tff(c_52, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_48])).
% 1.90/1.17  tff(c_75, plain, (![B_36, A_37, C_38]: (k1_xboole_0=B_36 | k1_relset_1(A_37, B_36, C_38)=A_37 | ~v1_funct_2(C_38, A_37, B_36) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_37, B_36))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.90/1.17  tff(c_78, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_75])).
% 1.90/1.17  tff(c_81, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_52, c_78])).
% 1.90/1.17  tff(c_82, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_24, c_81])).
% 1.90/1.17  tff(c_33, plain, (![C_15, A_16, B_17]: (v1_relat_1(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.90/1.17  tff(c_37, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_33])).
% 1.90/1.17  tff(c_32, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.90/1.17  tff(c_58, plain, (![B_25, A_26]: (r2_hidden(k1_funct_1(B_25, A_26), k2_relat_1(B_25)) | ~r2_hidden(A_26, k1_relat_1(B_25)) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.90/1.17  tff(c_38, plain, (![A_18, B_19, C_20]: (k2_relset_1(A_18, B_19, C_20)=k2_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.90/1.17  tff(c_42, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_38])).
% 1.90/1.17  tff(c_22, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_3'), k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.90/1.17  tff(c_43, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_22])).
% 1.90/1.17  tff(c_61, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_43])).
% 1.90/1.17  tff(c_64, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_32, c_61])).
% 1.90/1.17  tff(c_83, plain, (~r2_hidden('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_64])).
% 1.90/1.17  tff(c_87, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_83])).
% 1.90/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.17  
% 1.90/1.17  Inference rules
% 1.90/1.17  ----------------------
% 1.90/1.17  #Ref     : 0
% 1.90/1.17  #Sup     : 10
% 1.90/1.17  #Fact    : 0
% 1.90/1.17  #Define  : 0
% 1.90/1.17  #Split   : 0
% 1.90/1.17  #Chain   : 0
% 1.90/1.17  #Close   : 0
% 1.90/1.17  
% 1.90/1.17  Ordering : KBO
% 1.90/1.17  
% 1.90/1.17  Simplification rules
% 1.90/1.17  ----------------------
% 1.90/1.17  #Subsume      : 0
% 1.90/1.17  #Demod        : 10
% 1.90/1.17  #Tautology    : 5
% 1.90/1.18  #SimpNegUnit  : 2
% 1.90/1.18  #BackRed      : 3
% 1.90/1.18  
% 1.90/1.18  #Partial instantiations: 0
% 1.90/1.18  #Strategies tried      : 1
% 1.90/1.18  
% 1.90/1.18  Timing (in seconds)
% 1.90/1.18  ----------------------
% 1.90/1.18  Preprocessing        : 0.30
% 1.90/1.18  Parsing              : 0.16
% 1.90/1.18  CNF conversion       : 0.02
% 1.90/1.18  Main loop            : 0.11
% 1.90/1.18  Inferencing          : 0.04
% 1.90/1.18  Reduction            : 0.04
% 1.90/1.18  Demodulation         : 0.03
% 1.90/1.18  BG Simplification    : 0.01
% 1.90/1.18  Subsumption          : 0.02
% 1.90/1.18  Abstraction          : 0.00
% 1.90/1.18  MUC search           : 0.00
% 1.90/1.18  Cooper               : 0.00
% 1.90/1.18  Total                : 0.44
% 1.90/1.18  Index Insertion      : 0.00
% 1.90/1.18  Index Deletion       : 0.00
% 1.90/1.18  Index Matching       : 0.00
% 1.90/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------

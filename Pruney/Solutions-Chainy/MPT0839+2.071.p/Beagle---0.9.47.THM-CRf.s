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
% DateTime   : Thu Dec  3 10:08:31 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   54 (  91 expanded)
%              Number of leaves         :   26 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   71 ( 173 expanded)
%              Number of equality atoms :   22 (  47 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_22,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_8,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_35,plain,(
    ! [B_34,A_35] :
      ( v1_relat_1(B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_35))
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_38,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_35])).

tff(c_41,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_38])).

tff(c_12,plain,(
    ! [A_9] :
      ( k2_relat_1(A_9) = k1_xboole_0
      | k1_relat_1(A_9) != k1_xboole_0
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_45,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_41,c_12])).

tff(c_46,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_45])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1('#skF_1'(A_1,B_2),A_1)
      | k1_xboole_0 = B_2
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | k1_xboole_0 = B_2
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_101,plain,(
    ! [A_49,B_50,C_51] :
      ( k1_relset_1(A_49,B_50,C_51) = k1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_110,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_101])).

tff(c_20,plain,(
    ! [D_30] :
      ( ~ r2_hidden(D_30,k1_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ m1_subset_1(D_30,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_116,plain,(
    ! [D_52] :
      ( ~ r2_hidden(D_52,k1_relat_1('#skF_4'))
      | ~ m1_subset_1(D_52,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_20])).

tff(c_120,plain,(
    ! [A_1] :
      ( ~ m1_subset_1('#skF_1'(A_1,k1_relat_1('#skF_4')),'#skF_3')
      | k1_relat_1('#skF_4') = k1_xboole_0
      | ~ m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_2,c_116])).

tff(c_124,plain,(
    ! [A_53] :
      ( ~ m1_subset_1('#skF_1'(A_53,k1_relat_1('#skF_4')),'#skF_3')
      | ~ m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(A_53)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_120])).

tff(c_128,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | ~ m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_124])).

tff(c_131,plain,(
    ~ m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_128])).

tff(c_132,plain,(
    ! [A_54,B_55,C_56] :
      ( m1_subset_1(k1_relset_1(A_54,B_55,C_56),k1_zfmisc_1(A_54))
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_146,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_132])).

tff(c_151,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_146])).

tff(c_153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_151])).

tff(c_154,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_45])).

tff(c_213,plain,(
    ! [A_70,B_71,C_72] :
      ( k2_relset_1(A_70,B_71,C_72) = k2_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_220,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_213])).

tff(c_223,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_220])).

tff(c_225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_223])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:45:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.37  
% 2.15/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.38  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.15/1.38  
% 2.15/1.38  %Foreground sorts:
% 2.15/1.38  
% 2.15/1.38  
% 2.15/1.38  %Background operators:
% 2.15/1.38  
% 2.15/1.38  
% 2.15/1.38  %Foreground operators:
% 2.15/1.38  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.15/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.15/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.15/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.38  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.15/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.15/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.15/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.15/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.15/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.15/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.15/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.15/1.38  
% 2.15/1.39  tff(f_85, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relset_1)).
% 2.15/1.39  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.15/1.39  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.15/1.39  tff(f_52, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 2.15/1.39  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_subset_1)).
% 2.15/1.39  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.15/1.39  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.15/1.39  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.15/1.39  tff(c_22, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.15/1.39  tff(c_8, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.15/1.39  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.15/1.39  tff(c_35, plain, (![B_34, A_35]: (v1_relat_1(B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_35)) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.15/1.39  tff(c_38, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_35])).
% 2.15/1.39  tff(c_41, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_38])).
% 2.15/1.39  tff(c_12, plain, (![A_9]: (k2_relat_1(A_9)=k1_xboole_0 | k1_relat_1(A_9)!=k1_xboole_0 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.15/1.39  tff(c_45, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_41, c_12])).
% 2.15/1.39  tff(c_46, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_45])).
% 2.15/1.39  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1('#skF_1'(A_1, B_2), A_1) | k1_xboole_0=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.15/1.39  tff(c_2, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | k1_xboole_0=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.15/1.39  tff(c_101, plain, (![A_49, B_50, C_51]: (k1_relset_1(A_49, B_50, C_51)=k1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.15/1.39  tff(c_110, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_101])).
% 2.15/1.39  tff(c_20, plain, (![D_30]: (~r2_hidden(D_30, k1_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~m1_subset_1(D_30, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.15/1.39  tff(c_116, plain, (![D_52]: (~r2_hidden(D_52, k1_relat_1('#skF_4')) | ~m1_subset_1(D_52, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_20])).
% 2.15/1.39  tff(c_120, plain, (![A_1]: (~m1_subset_1('#skF_1'(A_1, k1_relat_1('#skF_4')), '#skF_3') | k1_relat_1('#skF_4')=k1_xboole_0 | ~m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_2, c_116])).
% 2.15/1.39  tff(c_124, plain, (![A_53]: (~m1_subset_1('#skF_1'(A_53, k1_relat_1('#skF_4')), '#skF_3') | ~m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(A_53)))), inference(negUnitSimplification, [status(thm)], [c_46, c_120])).
% 2.15/1.39  tff(c_128, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | ~m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_4, c_124])).
% 2.15/1.39  tff(c_131, plain, (~m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_128])).
% 2.15/1.39  tff(c_132, plain, (![A_54, B_55, C_56]: (m1_subset_1(k1_relset_1(A_54, B_55, C_56), k1_zfmisc_1(A_54)) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.15/1.39  tff(c_146, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_110, c_132])).
% 2.15/1.39  tff(c_151, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_146])).
% 2.15/1.39  tff(c_153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_151])).
% 2.15/1.39  tff(c_154, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_45])).
% 2.15/1.39  tff(c_213, plain, (![A_70, B_71, C_72]: (k2_relset_1(A_70, B_71, C_72)=k2_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.15/1.39  tff(c_220, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_213])).
% 2.15/1.39  tff(c_223, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_154, c_220])).
% 2.15/1.39  tff(c_225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_223])).
% 2.15/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.39  
% 2.15/1.39  Inference rules
% 2.15/1.39  ----------------------
% 2.15/1.39  #Ref     : 0
% 2.15/1.39  #Sup     : 39
% 2.15/1.39  #Fact    : 0
% 2.15/1.39  #Define  : 0
% 2.15/1.39  #Split   : 2
% 2.15/1.39  #Chain   : 0
% 2.15/1.39  #Close   : 0
% 2.15/1.39  
% 2.15/1.39  Ordering : KBO
% 2.15/1.39  
% 2.15/1.39  Simplification rules
% 2.15/1.39  ----------------------
% 2.15/1.39  #Subsume      : 1
% 2.15/1.39  #Demod        : 8
% 2.15/1.39  #Tautology    : 15
% 2.15/1.39  #SimpNegUnit  : 5
% 2.15/1.39  #BackRed      : 2
% 2.15/1.39  
% 2.15/1.39  #Partial instantiations: 0
% 2.15/1.39  #Strategies tried      : 1
% 2.15/1.39  
% 2.15/1.39  Timing (in seconds)
% 2.15/1.39  ----------------------
% 2.15/1.39  Preprocessing        : 0.41
% 2.15/1.39  Parsing              : 0.26
% 2.15/1.39  CNF conversion       : 0.02
% 2.15/1.39  Main loop            : 0.17
% 2.15/1.39  Inferencing          : 0.07
% 2.15/1.39  Reduction            : 0.05
% 2.15/1.39  Demodulation         : 0.03
% 2.15/1.39  BG Simplification    : 0.01
% 2.15/1.39  Subsumption          : 0.02
% 2.15/1.39  Abstraction          : 0.01
% 2.15/1.39  MUC search           : 0.00
% 2.15/1.39  Cooper               : 0.00
% 2.15/1.39  Total                : 0.61
% 2.15/1.39  Index Insertion      : 0.00
% 2.15/1.39  Index Deletion       : 0.00
% 2.15/1.39  Index Matching       : 0.00
% 2.15/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------

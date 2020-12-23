%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:21 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 115 expanded)
%              Number of leaves         :   26 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :   77 ( 227 expanded)
%              Number of equality atoms :   27 (  63 expanded)
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
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

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

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_22,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_8,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_35,plain,(
    ! [B_34,A_35] :
      ( v1_relat_1(B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_35))
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_38,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
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

tff(c_48,plain,(
    ! [A_37] :
      ( k1_relat_1(A_37) = k1_xboole_0
      | k2_relat_1(A_37) != k1_xboole_0
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_51,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_41,c_48])).

tff(c_57,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_51])).

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

tff(c_85,plain,(
    ! [A_46,B_47,C_48] :
      ( k2_relset_1(A_46,B_47,C_48) = k2_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_94,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_85])).

tff(c_20,plain,(
    ! [D_30] :
      ( ~ r2_hidden(D_30,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(D_30,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_100,plain,(
    ! [D_49] :
      ( ~ r2_hidden(D_49,k2_relat_1('#skF_4'))
      | ~ m1_subset_1(D_49,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_20])).

tff(c_104,plain,(
    ! [A_1] :
      ( ~ m1_subset_1('#skF_1'(A_1,k2_relat_1('#skF_4')),'#skF_3')
      | k2_relat_1('#skF_4') = k1_xboole_0
      | ~ m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_2,c_100])).

tff(c_108,plain,(
    ! [A_50] :
      ( ~ m1_subset_1('#skF_1'(A_50,k2_relat_1('#skF_4')),'#skF_3')
      | ~ m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1(A_50)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_104])).

tff(c_112,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | ~ m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_108])).

tff(c_115,plain,(
    ~ m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_112])).

tff(c_131,plain,(
    ! [A_54,B_55,C_56] :
      ( m1_subset_1(k2_relset_1(A_54,B_55,C_56),k1_zfmisc_1(B_55))
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_145,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_131])).

tff(c_150,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_145])).

tff(c_152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_150])).

tff(c_154,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_45])).

tff(c_201,plain,(
    ! [A_67,B_68,C_69] :
      ( k1_relset_1(A_67,B_68,C_69) = k1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_208,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_201])).

tff(c_211,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_208])).

tff(c_213,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_211])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:25:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.28  
% 2.00/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.28  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.00/1.28  
% 2.00/1.28  %Foreground sorts:
% 2.00/1.28  
% 2.00/1.28  
% 2.00/1.28  %Background operators:
% 2.00/1.28  
% 2.00/1.28  
% 2.00/1.28  %Foreground operators:
% 2.00/1.28  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.00/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.00/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.00/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.28  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.00/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.00/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.00/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.00/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.00/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.00/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.00/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.00/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.00/1.28  
% 2.00/1.30  tff(f_85, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 2.00/1.30  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.00/1.30  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.00/1.30  tff(f_52, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 2.00/1.30  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_subset_1)).
% 2.00/1.30  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.00/1.30  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.00/1.30  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.00/1.30  tff(c_22, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.00/1.30  tff(c_8, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.00/1.30  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.00/1.30  tff(c_35, plain, (![B_34, A_35]: (v1_relat_1(B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_35)) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.00/1.30  tff(c_38, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_35])).
% 2.00/1.30  tff(c_41, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_38])).
% 2.00/1.30  tff(c_12, plain, (![A_9]: (k2_relat_1(A_9)=k1_xboole_0 | k1_relat_1(A_9)!=k1_xboole_0 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.00/1.30  tff(c_45, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_41, c_12])).
% 2.00/1.30  tff(c_46, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_45])).
% 2.00/1.30  tff(c_48, plain, (![A_37]: (k1_relat_1(A_37)=k1_xboole_0 | k2_relat_1(A_37)!=k1_xboole_0 | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.00/1.30  tff(c_51, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_41, c_48])).
% 2.00/1.30  tff(c_57, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_46, c_51])).
% 2.00/1.30  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1('#skF_1'(A_1, B_2), A_1) | k1_xboole_0=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.00/1.30  tff(c_2, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | k1_xboole_0=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.00/1.30  tff(c_85, plain, (![A_46, B_47, C_48]: (k2_relset_1(A_46, B_47, C_48)=k2_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.00/1.30  tff(c_94, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_85])).
% 2.00/1.30  tff(c_20, plain, (![D_30]: (~r2_hidden(D_30, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(D_30, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.00/1.30  tff(c_100, plain, (![D_49]: (~r2_hidden(D_49, k2_relat_1('#skF_4')) | ~m1_subset_1(D_49, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_20])).
% 2.00/1.30  tff(c_104, plain, (![A_1]: (~m1_subset_1('#skF_1'(A_1, k2_relat_1('#skF_4')), '#skF_3') | k2_relat_1('#skF_4')=k1_xboole_0 | ~m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_2, c_100])).
% 2.00/1.30  tff(c_108, plain, (![A_50]: (~m1_subset_1('#skF_1'(A_50, k2_relat_1('#skF_4')), '#skF_3') | ~m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1(A_50)))), inference(negUnitSimplification, [status(thm)], [c_57, c_104])).
% 2.00/1.30  tff(c_112, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | ~m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_4, c_108])).
% 2.00/1.30  tff(c_115, plain, (~m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_57, c_112])).
% 2.00/1.30  tff(c_131, plain, (![A_54, B_55, C_56]: (m1_subset_1(k2_relset_1(A_54, B_55, C_56), k1_zfmisc_1(B_55)) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.00/1.30  tff(c_145, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_94, c_131])).
% 2.00/1.30  tff(c_150, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_145])).
% 2.00/1.30  tff(c_152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_115, c_150])).
% 2.00/1.30  tff(c_154, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_45])).
% 2.00/1.30  tff(c_201, plain, (![A_67, B_68, C_69]: (k1_relset_1(A_67, B_68, C_69)=k1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.00/1.30  tff(c_208, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_201])).
% 2.00/1.30  tff(c_211, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_154, c_208])).
% 2.00/1.30  tff(c_213, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_211])).
% 2.00/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.30  
% 2.00/1.30  Inference rules
% 2.00/1.30  ----------------------
% 2.00/1.30  #Ref     : 0
% 2.00/1.30  #Sup     : 37
% 2.00/1.30  #Fact    : 0
% 2.00/1.30  #Define  : 0
% 2.00/1.30  #Split   : 1
% 2.00/1.30  #Chain   : 0
% 2.00/1.30  #Close   : 0
% 2.00/1.30  
% 2.00/1.30  Ordering : KBO
% 2.00/1.30  
% 2.00/1.30  Simplification rules
% 2.00/1.30  ----------------------
% 2.00/1.30  #Subsume      : 1
% 2.00/1.30  #Demod        : 7
% 2.00/1.30  #Tautology    : 15
% 2.00/1.30  #SimpNegUnit  : 5
% 2.00/1.30  #BackRed      : 2
% 2.00/1.30  
% 2.00/1.30  #Partial instantiations: 0
% 2.00/1.30  #Strategies tried      : 1
% 2.00/1.30  
% 2.00/1.30  Timing (in seconds)
% 2.00/1.30  ----------------------
% 2.00/1.30  Preprocessing        : 0.31
% 2.00/1.30  Parsing              : 0.18
% 2.00/1.30  CNF conversion       : 0.02
% 2.00/1.30  Main loop            : 0.16
% 2.00/1.30  Inferencing          : 0.07
% 2.00/1.30  Reduction            : 0.05
% 2.00/1.30  Demodulation         : 0.03
% 2.00/1.30  BG Simplification    : 0.01
% 2.00/1.30  Subsumption          : 0.02
% 2.00/1.30  Abstraction          : 0.01
% 2.00/1.30  MUC search           : 0.00
% 2.00/1.30  Cooper               : 0.00
% 2.00/1.30  Total                : 0.51
% 2.00/1.30  Index Insertion      : 0.00
% 2.00/1.30  Index Deletion       : 0.00
% 2.00/1.30  Index Matching       : 0.00
% 2.00/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------

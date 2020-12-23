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
% DateTime   : Thu Dec  3 10:08:13 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   52 (  84 expanded)
%              Number of leaves         :   26 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :   64 ( 154 expanded)
%              Number of equality atoms :   21 (  47 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,negated_conjecture,(
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

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_20,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_28,plain,(
    ! [C_32,A_33,B_34] :
      ( v1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_32,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_28])).

tff(c_33,plain,(
    ! [A_35] :
      ( k1_relat_1(A_35) = k1_xboole_0
      | k2_relat_1(A_35) != k1_xboole_0
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_37,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_33])).

tff(c_38,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_37])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_57,plain,(
    ! [A_42,B_43,C_44] :
      ( k2_relset_1(A_42,B_43,C_44) = k2_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_61,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_57])).

tff(c_18,plain,(
    ! [D_30] :
      ( ~ r2_hidden(D_30,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(D_30,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_67,plain,(
    ! [D_45] :
      ( ~ r2_hidden(D_45,k2_relat_1('#skF_4'))
      | ~ m1_subset_1(D_45,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_18])).

tff(c_71,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_4')),'#skF_3')
    | k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_67])).

tff(c_74,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_4')),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_71])).

tff(c_87,plain,(
    ! [A_49,B_50,C_51] :
      ( m1_subset_1(k2_relset_1(A_49,B_50,C_51),k1_zfmisc_1(B_50))
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_104,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_87])).

tff(c_110,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_104])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( m1_subset_1(A_3,C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_114,plain,(
    ! [A_52] :
      ( m1_subset_1(A_52,'#skF_3')
      | ~ r2_hidden(A_52,k2_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_110,c_4])).

tff(c_118,plain,
    ( m1_subset_1('#skF_1'(k2_relat_1('#skF_4')),'#skF_3')
    | k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_114])).

tff(c_122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_74,c_118])).

tff(c_123,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_37])).

tff(c_151,plain,(
    ! [A_59,B_60,C_61] :
      ( k1_relset_1(A_59,B_60,C_61) = k1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_154,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_151])).

tff(c_156,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_154])).

tff(c_158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_156])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:25:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.25  
% 1.94/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.25  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 1.94/1.25  
% 1.94/1.25  %Foreground sorts:
% 1.94/1.25  
% 1.94/1.25  
% 1.94/1.25  %Background operators:
% 1.94/1.25  
% 1.94/1.25  
% 1.94/1.25  %Foreground operators:
% 1.94/1.25  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.94/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.94/1.25  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.94/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.94/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.25  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.94/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.94/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.94/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.94/1.25  tff('#skF_4', type, '#skF_4': $i).
% 1.94/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.94/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.94/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.94/1.25  
% 1.94/1.26  tff(f_82, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 1.94/1.26  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.94/1.26  tff(f_45, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 1.94/1.26  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.94/1.26  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 1.94/1.26  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 1.94/1.26  tff(f_39, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 1.94/1.26  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.94/1.26  tff(c_20, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.94/1.26  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.94/1.26  tff(c_28, plain, (![C_32, A_33, B_34]: (v1_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.94/1.26  tff(c_32, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_28])).
% 1.94/1.26  tff(c_33, plain, (![A_35]: (k1_relat_1(A_35)=k1_xboole_0 | k2_relat_1(A_35)!=k1_xboole_0 | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.94/1.26  tff(c_37, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_33])).
% 1.94/1.26  tff(c_38, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_37])).
% 1.94/1.26  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.94/1.26  tff(c_57, plain, (![A_42, B_43, C_44]: (k2_relset_1(A_42, B_43, C_44)=k2_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.94/1.26  tff(c_61, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_57])).
% 1.94/1.26  tff(c_18, plain, (![D_30]: (~r2_hidden(D_30, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(D_30, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.94/1.26  tff(c_67, plain, (![D_45]: (~r2_hidden(D_45, k2_relat_1('#skF_4')) | ~m1_subset_1(D_45, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_18])).
% 1.94/1.26  tff(c_71, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_4')), '#skF_3') | k2_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_67])).
% 1.94/1.26  tff(c_74, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_4')), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_38, c_71])).
% 1.94/1.26  tff(c_87, plain, (![A_49, B_50, C_51]: (m1_subset_1(k2_relset_1(A_49, B_50, C_51), k1_zfmisc_1(B_50)) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.94/1.26  tff(c_104, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_61, c_87])).
% 1.94/1.26  tff(c_110, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_104])).
% 1.94/1.26  tff(c_4, plain, (![A_3, C_5, B_4]: (m1_subset_1(A_3, C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.94/1.26  tff(c_114, plain, (![A_52]: (m1_subset_1(A_52, '#skF_3') | ~r2_hidden(A_52, k2_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_110, c_4])).
% 1.94/1.26  tff(c_118, plain, (m1_subset_1('#skF_1'(k2_relat_1('#skF_4')), '#skF_3') | k2_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_114])).
% 1.94/1.26  tff(c_122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_74, c_118])).
% 1.94/1.26  tff(c_123, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_37])).
% 1.94/1.26  tff(c_151, plain, (![A_59, B_60, C_61]: (k1_relset_1(A_59, B_60, C_61)=k1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.94/1.26  tff(c_154, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_151])).
% 1.94/1.26  tff(c_156, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_123, c_154])).
% 1.94/1.26  tff(c_158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_156])).
% 1.94/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.26  
% 1.94/1.26  Inference rules
% 1.94/1.26  ----------------------
% 1.94/1.26  #Ref     : 0
% 1.94/1.26  #Sup     : 27
% 1.94/1.26  #Fact    : 0
% 1.94/1.26  #Define  : 0
% 1.94/1.26  #Split   : 1
% 1.94/1.26  #Chain   : 0
% 1.94/1.26  #Close   : 0
% 1.94/1.26  
% 1.94/1.26  Ordering : KBO
% 1.94/1.26  
% 1.94/1.26  Simplification rules
% 1.94/1.26  ----------------------
% 1.94/1.26  #Subsume      : 2
% 1.94/1.26  #Demod        : 8
% 1.94/1.26  #Tautology    : 9
% 1.94/1.26  #SimpNegUnit  : 5
% 1.94/1.26  #BackRed      : 2
% 1.94/1.26  
% 1.94/1.26  #Partial instantiations: 0
% 1.94/1.26  #Strategies tried      : 1
% 1.94/1.26  
% 1.94/1.26  Timing (in seconds)
% 1.94/1.26  ----------------------
% 1.94/1.27  Preprocessing        : 0.31
% 1.94/1.27  Parsing              : 0.17
% 1.94/1.27  CNF conversion       : 0.02
% 1.94/1.27  Main loop            : 0.15
% 1.94/1.27  Inferencing          : 0.06
% 1.94/1.27  Reduction            : 0.04
% 1.94/1.27  Demodulation         : 0.03
% 1.94/1.27  BG Simplification    : 0.01
% 1.94/1.27  Subsumption          : 0.02
% 1.94/1.27  Abstraction          : 0.01
% 1.94/1.27  MUC search           : 0.00
% 1.94/1.27  Cooper               : 0.00
% 1.94/1.27  Total                : 0.48
% 1.94/1.27  Index Insertion      : 0.00
% 1.94/1.27  Index Deletion       : 0.00
% 1.94/1.27  Index Matching       : 0.00
% 1.94/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------

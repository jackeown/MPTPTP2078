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
% DateTime   : Thu Dec  3 10:08:21 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   56 (  89 expanded)
%              Number of leaves         :   28 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   75 ( 168 expanded)
%              Number of equality atoms :   13 (  32 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
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

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k1_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_61,axiom,(
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

tff(c_22,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_48,plain,(
    ! [A_45,B_46,C_47] :
      ( k1_relset_1(A_45,B_46,C_47) = k1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_52,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_48])).

tff(c_20,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_53,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_20])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_29,plain,(
    ! [B_38,A_39] :
      ( v1_relat_1(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_39))
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_32,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_22,c_29])).

tff(c_35,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_32])).

tff(c_10,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_2'(A_11,B_12),k2_relat_1(B_12))
      | ~ r2_hidden(A_11,k1_relat_1(B_12))
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_59,plain,(
    ! [A_50,B_51,C_52] :
      ( k2_relset_1(A_50,B_51,C_52) = k2_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_63,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_59])).

tff(c_18,plain,(
    ! [D_34] :
      ( ~ r2_hidden(D_34,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_34,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_70,plain,(
    ! [D_53] :
      ( ~ r2_hidden(D_53,k2_relat_1('#skF_5'))
      | ~ m1_subset_1(D_53,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_18])).

tff(c_74,plain,(
    ! [A_11] :
      ( ~ m1_subset_1('#skF_2'(A_11,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_11,k1_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_10,c_70])).

tff(c_83,plain,(
    ! [A_54] :
      ( ~ m1_subset_1('#skF_2'(A_54,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_54,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_74])).

tff(c_87,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')),'#skF_5'),'#skF_4')
    | k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_83])).

tff(c_90,plain,(
    ~ m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')),'#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_87])).

tff(c_91,plain,(
    ! [A_55,B_56,C_57] :
      ( m1_subset_1(k2_relset_1(A_55,B_56,C_57),k1_zfmisc_1(B_56))
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_107,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_91])).

tff(c_113,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_107])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( m1_subset_1(A_3,C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_133,plain,(
    ! [A_61] :
      ( m1_subset_1(A_61,'#skF_4')
      | ~ r2_hidden(A_61,k2_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_113,c_4])).

tff(c_137,plain,(
    ! [A_11] :
      ( m1_subset_1('#skF_2'(A_11,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_11,k1_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_10,c_133])).

tff(c_202,plain,(
    ! [A_68] :
      ( m1_subset_1('#skF_2'(A_68,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_68,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_137])).

tff(c_206,plain,
    ( m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')),'#skF_5'),'#skF_4')
    | k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_202])).

tff(c_210,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_90,c_206])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 10:04:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.21  
% 2.07/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.21  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.07/1.21  
% 2.07/1.21  %Foreground sorts:
% 2.07/1.21  
% 2.07/1.21  
% 2.07/1.21  %Background operators:
% 2.07/1.21  
% 2.07/1.21  
% 2.07/1.21  %Foreground operators:
% 2.07/1.21  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.07/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.21  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.07/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.07/1.21  tff('#skF_5', type, '#skF_5': $i).
% 2.07/1.21  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.21  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.07/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.07/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.07/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.07/1.21  tff('#skF_4', type, '#skF_4': $i).
% 2.07/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.07/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.07/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.07/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.07/1.21  
% 2.07/1.23  tff(f_90, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 2.07/1.23  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.07/1.23  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.07/1.23  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.07/1.23  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.07/1.23  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k1_relat_1(B)) & (![C]: ~r2_hidden(C, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_relat_1)).
% 2.07/1.23  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.07/1.23  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.07/1.23  tff(f_39, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.07/1.23  tff(c_22, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.07/1.23  tff(c_48, plain, (![A_45, B_46, C_47]: (k1_relset_1(A_45, B_46, C_47)=k1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.07/1.23  tff(c_52, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_48])).
% 2.07/1.23  tff(c_20, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.07/1.23  tff(c_53, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_20])).
% 2.07/1.23  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.07/1.23  tff(c_8, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.07/1.23  tff(c_29, plain, (![B_38, A_39]: (v1_relat_1(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_39)) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.07/1.23  tff(c_32, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_22, c_29])).
% 2.07/1.23  tff(c_35, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_32])).
% 2.07/1.23  tff(c_10, plain, (![A_11, B_12]: (r2_hidden('#skF_2'(A_11, B_12), k2_relat_1(B_12)) | ~r2_hidden(A_11, k1_relat_1(B_12)) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.07/1.23  tff(c_59, plain, (![A_50, B_51, C_52]: (k2_relset_1(A_50, B_51, C_52)=k2_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.07/1.23  tff(c_63, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_59])).
% 2.07/1.23  tff(c_18, plain, (![D_34]: (~r2_hidden(D_34, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_34, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.07/1.23  tff(c_70, plain, (![D_53]: (~r2_hidden(D_53, k2_relat_1('#skF_5')) | ~m1_subset_1(D_53, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_18])).
% 2.07/1.23  tff(c_74, plain, (![A_11]: (~m1_subset_1('#skF_2'(A_11, '#skF_5'), '#skF_4') | ~r2_hidden(A_11, k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_10, c_70])).
% 2.07/1.23  tff(c_83, plain, (![A_54]: (~m1_subset_1('#skF_2'(A_54, '#skF_5'), '#skF_4') | ~r2_hidden(A_54, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_74])).
% 2.07/1.23  tff(c_87, plain, (~m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')), '#skF_5'), '#skF_4') | k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_83])).
% 2.07/1.23  tff(c_90, plain, (~m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')), '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_53, c_87])).
% 2.07/1.23  tff(c_91, plain, (![A_55, B_56, C_57]: (m1_subset_1(k2_relset_1(A_55, B_56, C_57), k1_zfmisc_1(B_56)) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.07/1.23  tff(c_107, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_63, c_91])).
% 2.07/1.23  tff(c_113, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_107])).
% 2.07/1.23  tff(c_4, plain, (![A_3, C_5, B_4]: (m1_subset_1(A_3, C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.07/1.23  tff(c_133, plain, (![A_61]: (m1_subset_1(A_61, '#skF_4') | ~r2_hidden(A_61, k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_113, c_4])).
% 2.07/1.23  tff(c_137, plain, (![A_11]: (m1_subset_1('#skF_2'(A_11, '#skF_5'), '#skF_4') | ~r2_hidden(A_11, k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_10, c_133])).
% 2.07/1.23  tff(c_202, plain, (![A_68]: (m1_subset_1('#skF_2'(A_68, '#skF_5'), '#skF_4') | ~r2_hidden(A_68, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_137])).
% 2.07/1.23  tff(c_206, plain, (m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')), '#skF_5'), '#skF_4') | k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_202])).
% 2.07/1.23  tff(c_210, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_90, c_206])).
% 2.07/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.23  
% 2.07/1.23  Inference rules
% 2.07/1.23  ----------------------
% 2.07/1.23  #Ref     : 0
% 2.07/1.23  #Sup     : 36
% 2.07/1.23  #Fact    : 0
% 2.07/1.23  #Define  : 0
% 2.07/1.23  #Split   : 2
% 2.07/1.23  #Chain   : 0
% 2.07/1.23  #Close   : 0
% 2.07/1.23  
% 2.07/1.23  Ordering : KBO
% 2.07/1.23  
% 2.07/1.23  Simplification rules
% 2.07/1.23  ----------------------
% 2.07/1.23  #Subsume      : 6
% 2.07/1.23  #Demod        : 17
% 2.07/1.23  #Tautology    : 10
% 2.07/1.23  #SimpNegUnit  : 4
% 2.07/1.23  #BackRed      : 8
% 2.07/1.23  
% 2.07/1.23  #Partial instantiations: 0
% 2.07/1.23  #Strategies tried      : 1
% 2.07/1.23  
% 2.07/1.23  Timing (in seconds)
% 2.07/1.23  ----------------------
% 2.07/1.23  Preprocessing        : 0.30
% 2.07/1.23  Parsing              : 0.17
% 2.07/1.23  CNF conversion       : 0.02
% 2.07/1.23  Main loop            : 0.17
% 2.07/1.23  Inferencing          : 0.07
% 2.07/1.23  Reduction            : 0.05
% 2.07/1.23  Demodulation         : 0.04
% 2.07/1.23  BG Simplification    : 0.01
% 2.07/1.23  Subsumption          : 0.02
% 2.07/1.23  Abstraction          : 0.01
% 2.07/1.23  MUC search           : 0.00
% 2.07/1.23  Cooper               : 0.00
% 2.07/1.23  Total                : 0.50
% 2.07/1.23  Index Insertion      : 0.00
% 2.07/1.23  Index Deletion       : 0.00
% 2.07/1.23  Index Matching       : 0.00
% 2.07/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------

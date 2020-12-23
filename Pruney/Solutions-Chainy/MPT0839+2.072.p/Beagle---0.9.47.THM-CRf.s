%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:31 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 114 expanded)
%              Number of leaves         :   28 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :   81 ( 227 expanded)
%              Number of equality atoms :   17 (  42 expanded)
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
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(c_20,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_22,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_80,plain,(
    ! [A_52,B_53,C_54] :
      ( k2_relset_1(A_52,B_53,C_54) = k2_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_84,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_80])).

tff(c_85,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_20])).

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
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_29])).

tff(c_35,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_32])).

tff(c_10,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_2'(A_11,B_12),k1_relat_1(B_12))
      | ~ r2_hidden(A_11,k2_relat_1(B_12))
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_48,plain,(
    ! [A_45,B_46,C_47] :
      ( k1_relset_1(A_45,B_46,C_47) = k1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_52,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_48])).

tff(c_18,plain,(
    ! [D_34] :
      ( ~ r2_hidden(D_34,k1_relset_1('#skF_4','#skF_3','#skF_5'))
      | ~ m1_subset_1(D_34,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_60,plain,(
    ! [D_50] :
      ( ~ r2_hidden(D_50,k1_relat_1('#skF_5'))
      | ~ m1_subset_1(D_50,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_18])).

tff(c_64,plain,(
    ! [A_11] :
      ( ~ m1_subset_1('#skF_2'(A_11,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_11,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_10,c_60])).

tff(c_73,plain,(
    ! [A_51] :
      ( ~ m1_subset_1('#skF_2'(A_51,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_51,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_64])).

tff(c_78,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_1'(k2_relat_1('#skF_5')),'#skF_5'),'#skF_4')
    | k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_73])).

tff(c_79,plain,(
    ~ m1_subset_1('#skF_2'('#skF_1'(k2_relat_1('#skF_5')),'#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_90,plain,(
    ! [A_55,B_56,C_57] :
      ( m1_subset_1(k1_relset_1(A_55,B_56,C_57),k1_zfmisc_1(A_55))
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_106,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_90])).

tff(c_112,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_106])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( m1_subset_1(A_3,C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_132,plain,(
    ! [A_61] :
      ( m1_subset_1(A_61,'#skF_4')
      | ~ r2_hidden(A_61,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_112,c_4])).

tff(c_136,plain,(
    ! [A_11] :
      ( m1_subset_1('#skF_2'(A_11,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_11,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_10,c_132])).

tff(c_201,plain,(
    ! [A_68] :
      ( m1_subset_1('#skF_2'(A_68,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_68,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_136])).

tff(c_205,plain,
    ( m1_subset_1('#skF_2'('#skF_1'(k2_relat_1('#skF_5')),'#skF_5'),'#skF_4')
    | k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_201])).

tff(c_209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_79,c_205])).

tff(c_210,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_228,plain,(
    ! [A_70,B_71,C_72] :
      ( k2_relset_1(A_70,B_71,C_72) = k2_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_231,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_228])).

tff(c_233,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_231])).

tff(c_235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_233])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:28:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.23  
% 1.98/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.23  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 1.98/1.23  
% 1.98/1.23  %Foreground sorts:
% 1.98/1.23  
% 1.98/1.23  
% 1.98/1.23  %Background operators:
% 1.98/1.23  
% 1.98/1.23  
% 1.98/1.23  %Foreground operators:
% 1.98/1.23  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.98/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.98/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.98/1.23  tff('#skF_5', type, '#skF_5': $i).
% 1.98/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.23  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.98/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.98/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.98/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.98/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.98/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.98/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.98/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.23  
% 2.18/1.24  tff(f_90, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 2.18/1.24  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.18/1.24  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.18/1.24  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.18/1.24  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.18/1.24  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relat_1)).
% 2.18/1.24  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.18/1.24  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.18/1.24  tff(f_39, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.18/1.24  tff(c_20, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.18/1.24  tff(c_22, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.18/1.24  tff(c_80, plain, (![A_52, B_53, C_54]: (k2_relset_1(A_52, B_53, C_54)=k2_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.18/1.24  tff(c_84, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_80])).
% 2.18/1.24  tff(c_85, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_84, c_20])).
% 2.18/1.24  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.18/1.24  tff(c_8, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.18/1.24  tff(c_29, plain, (![B_38, A_39]: (v1_relat_1(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_39)) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.18/1.24  tff(c_32, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_29])).
% 2.18/1.24  tff(c_35, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_32])).
% 2.18/1.24  tff(c_10, plain, (![A_11, B_12]: (r2_hidden('#skF_2'(A_11, B_12), k1_relat_1(B_12)) | ~r2_hidden(A_11, k2_relat_1(B_12)) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.18/1.24  tff(c_48, plain, (![A_45, B_46, C_47]: (k1_relset_1(A_45, B_46, C_47)=k1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.18/1.24  tff(c_52, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_48])).
% 2.18/1.24  tff(c_18, plain, (![D_34]: (~r2_hidden(D_34, k1_relset_1('#skF_4', '#skF_3', '#skF_5')) | ~m1_subset_1(D_34, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.18/1.24  tff(c_60, plain, (![D_50]: (~r2_hidden(D_50, k1_relat_1('#skF_5')) | ~m1_subset_1(D_50, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_18])).
% 2.18/1.24  tff(c_64, plain, (![A_11]: (~m1_subset_1('#skF_2'(A_11, '#skF_5'), '#skF_4') | ~r2_hidden(A_11, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_10, c_60])).
% 2.18/1.24  tff(c_73, plain, (![A_51]: (~m1_subset_1('#skF_2'(A_51, '#skF_5'), '#skF_4') | ~r2_hidden(A_51, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_64])).
% 2.18/1.24  tff(c_78, plain, (~m1_subset_1('#skF_2'('#skF_1'(k2_relat_1('#skF_5')), '#skF_5'), '#skF_4') | k2_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_73])).
% 2.18/1.24  tff(c_79, plain, (~m1_subset_1('#skF_2'('#skF_1'(k2_relat_1('#skF_5')), '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_78])).
% 2.18/1.24  tff(c_90, plain, (![A_55, B_56, C_57]: (m1_subset_1(k1_relset_1(A_55, B_56, C_57), k1_zfmisc_1(A_55)) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.18/1.24  tff(c_106, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_52, c_90])).
% 2.18/1.24  tff(c_112, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_106])).
% 2.18/1.24  tff(c_4, plain, (![A_3, C_5, B_4]: (m1_subset_1(A_3, C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.18/1.24  tff(c_132, plain, (![A_61]: (m1_subset_1(A_61, '#skF_4') | ~r2_hidden(A_61, k1_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_112, c_4])).
% 2.18/1.24  tff(c_136, plain, (![A_11]: (m1_subset_1('#skF_2'(A_11, '#skF_5'), '#skF_4') | ~r2_hidden(A_11, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_10, c_132])).
% 2.18/1.24  tff(c_201, plain, (![A_68]: (m1_subset_1('#skF_2'(A_68, '#skF_5'), '#skF_4') | ~r2_hidden(A_68, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_136])).
% 2.18/1.24  tff(c_205, plain, (m1_subset_1('#skF_2'('#skF_1'(k2_relat_1('#skF_5')), '#skF_5'), '#skF_4') | k2_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_201])).
% 2.18/1.24  tff(c_209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_79, c_205])).
% 2.18/1.24  tff(c_210, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_78])).
% 2.18/1.24  tff(c_228, plain, (![A_70, B_71, C_72]: (k2_relset_1(A_70, B_71, C_72)=k2_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.18/1.24  tff(c_231, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_228])).
% 2.18/1.24  tff(c_233, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_210, c_231])).
% 2.18/1.24  tff(c_235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_233])).
% 2.18/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.24  
% 2.18/1.24  Inference rules
% 2.18/1.24  ----------------------
% 2.18/1.24  #Ref     : 0
% 2.18/1.24  #Sup     : 41
% 2.18/1.24  #Fact    : 0
% 2.18/1.24  #Define  : 0
% 2.18/1.24  #Split   : 3
% 2.18/1.24  #Chain   : 0
% 2.18/1.24  #Close   : 0
% 2.18/1.24  
% 2.18/1.24  Ordering : KBO
% 2.18/1.24  
% 2.18/1.24  Simplification rules
% 2.18/1.24  ----------------------
% 2.18/1.24  #Subsume      : 6
% 2.18/1.24  #Demod        : 20
% 2.18/1.24  #Tautology    : 13
% 2.18/1.24  #SimpNegUnit  : 4
% 2.18/1.24  #BackRed      : 9
% 2.18/1.25  
% 2.18/1.25  #Partial instantiations: 0
% 2.18/1.25  #Strategies tried      : 1
% 2.18/1.25  
% 2.18/1.25  Timing (in seconds)
% 2.18/1.25  ----------------------
% 2.18/1.25  Preprocessing        : 0.30
% 2.18/1.25  Parsing              : 0.16
% 2.18/1.25  CNF conversion       : 0.02
% 2.18/1.25  Main loop            : 0.19
% 2.18/1.25  Inferencing          : 0.08
% 2.18/1.25  Reduction            : 0.06
% 2.18/1.25  Demodulation         : 0.04
% 2.18/1.25  BG Simplification    : 0.01
% 2.18/1.25  Subsumption          : 0.03
% 2.18/1.25  Abstraction          : 0.01
% 2.18/1.25  MUC search           : 0.00
% 2.18/1.25  Cooper               : 0.00
% 2.18/1.25  Total                : 0.52
% 2.18/1.25  Index Insertion      : 0.00
% 2.18/1.25  Index Deletion       : 0.00
% 2.18/1.25  Index Matching       : 0.00
% 2.18/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------

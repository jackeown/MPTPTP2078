%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:21 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 107 expanded)
%              Number of leaves         :   31 (  49 expanded)
%              Depth                    :    7
%              Number of atoms          :   85 ( 198 expanded)
%              Number of equality atoms :   24 (  51 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
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
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_32,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_16,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_47,plain,(
    ! [B_43,A_44] :
      ( v1_relat_1(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44))
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_50,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_34,c_47])).

tff(c_53,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_50])).

tff(c_18,plain,(
    ! [A_13] :
      ( k1_relat_1(A_13) = k1_xboole_0
      | k2_relat_1(A_13) != k1_xboole_0
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_58,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_53,c_18])).

tff(c_59,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_10,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_102,plain,(
    ! [A_61,B_62] :
      ( r2_hidden('#skF_1'(A_61,B_62),B_62)
      | r2_hidden('#skF_2'(A_61,B_62),A_61)
      | B_62 = A_61 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    ! [B_15,A_14] :
      ( ~ r1_tarski(B_15,A_14)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_201,plain,(
    ! [B_75,A_76] :
      ( ~ r1_tarski(B_75,'#skF_1'(A_76,B_75))
      | r2_hidden('#skF_2'(A_76,B_75),A_76)
      | B_75 = A_76 ) ),
    inference(resolution,[status(thm)],[c_102,c_22])).

tff(c_206,plain,(
    ! [A_77] :
      ( r2_hidden('#skF_2'(A_77,k1_xboole_0),A_77)
      | k1_xboole_0 = A_77 ) ),
    inference(resolution,[status(thm)],[c_10,c_201])).

tff(c_91,plain,(
    ! [A_57,B_58,C_59] :
      ( k2_relset_1(A_57,B_58,C_59) = k2_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_95,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_91])).

tff(c_30,plain,(
    ! [D_36] :
      ( ~ r2_hidden(D_36,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_36,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_96,plain,(
    ! [D_36] :
      ( ~ r2_hidden(D_36,k2_relat_1('#skF_5'))
      | ~ m1_subset_1(D_36,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_30])).

tff(c_210,plain,
    ( ~ m1_subset_1('#skF_2'(k2_relat_1('#skF_5'),k1_xboole_0),'#skF_4')
    | k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_206,c_96])).

tff(c_220,plain,(
    ~ m1_subset_1('#skF_2'(k2_relat_1('#skF_5'),k1_xboole_0),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_210])).

tff(c_205,plain,(
    ! [A_76] :
      ( r2_hidden('#skF_2'(A_76,k1_xboole_0),A_76)
      | k1_xboole_0 = A_76 ) ),
    inference(resolution,[status(thm)],[c_10,c_201])).

tff(c_223,plain,(
    ! [A_78,B_79,C_80] :
      ( m1_subset_1(k2_relset_1(A_78,B_79,C_80),k1_zfmisc_1(B_79))
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_239,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_223])).

tff(c_245,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_239])).

tff(c_12,plain,(
    ! [A_5,C_7,B_6] :
      ( m1_subset_1(A_5,C_7)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(C_7))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_276,plain,(
    ! [A_83] :
      ( m1_subset_1(A_83,'#skF_4')
      | ~ r2_hidden(A_83,k2_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_245,c_12])).

tff(c_284,plain,
    ( m1_subset_1('#skF_2'(k2_relat_1('#skF_5'),k1_xboole_0),'#skF_4')
    | k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_205,c_276])).

tff(c_310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_220,c_284])).

tff(c_311,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_395,plain,(
    ! [A_101,B_102,C_103] :
      ( k1_relset_1(A_101,B_102,C_103) = k1_relat_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_398,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_395])).

tff(c_400,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_398])).

tff(c_402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_400])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n023.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 17:32:20 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.33  
% 2.35/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.33  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.35/1.33  
% 2.35/1.33  %Foreground sorts:
% 2.35/1.33  
% 2.35/1.33  
% 2.35/1.33  %Background operators:
% 2.35/1.33  
% 2.35/1.33  
% 2.35/1.33  %Foreground operators:
% 2.35/1.33  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.35/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.35/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.35/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.35/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.35/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.35/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.35/1.33  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.35/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.35/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.35/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.35/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.35/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.35/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.35/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.35/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.35/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.35/1.33  
% 2.35/1.34  tff(f_93, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 2.35/1.34  tff(f_49, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.35/1.34  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.35/1.34  tff(f_55, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 2.35/1.34  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.35/1.34  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 2.35/1.34  tff(f_60, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.35/1.34  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.35/1.34  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.35/1.34  tff(f_40, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.35/1.34  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.35/1.34  tff(c_32, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.35/1.34  tff(c_16, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.35/1.34  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.35/1.34  tff(c_47, plain, (![B_43, A_44]: (v1_relat_1(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.35/1.34  tff(c_50, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_47])).
% 2.35/1.34  tff(c_53, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_50])).
% 2.35/1.34  tff(c_18, plain, (![A_13]: (k1_relat_1(A_13)=k1_xboole_0 | k2_relat_1(A_13)!=k1_xboole_0 | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.35/1.34  tff(c_58, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_53, c_18])).
% 2.35/1.34  tff(c_59, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_58])).
% 2.35/1.34  tff(c_10, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.35/1.34  tff(c_102, plain, (![A_61, B_62]: (r2_hidden('#skF_1'(A_61, B_62), B_62) | r2_hidden('#skF_2'(A_61, B_62), A_61) | B_62=A_61)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.35/1.34  tff(c_22, plain, (![B_15, A_14]: (~r1_tarski(B_15, A_14) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.35/1.34  tff(c_201, plain, (![B_75, A_76]: (~r1_tarski(B_75, '#skF_1'(A_76, B_75)) | r2_hidden('#skF_2'(A_76, B_75), A_76) | B_75=A_76)), inference(resolution, [status(thm)], [c_102, c_22])).
% 2.35/1.34  tff(c_206, plain, (![A_77]: (r2_hidden('#skF_2'(A_77, k1_xboole_0), A_77) | k1_xboole_0=A_77)), inference(resolution, [status(thm)], [c_10, c_201])).
% 2.35/1.34  tff(c_91, plain, (![A_57, B_58, C_59]: (k2_relset_1(A_57, B_58, C_59)=k2_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.35/1.34  tff(c_95, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_91])).
% 2.35/1.34  tff(c_30, plain, (![D_36]: (~r2_hidden(D_36, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_36, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.35/1.34  tff(c_96, plain, (![D_36]: (~r2_hidden(D_36, k2_relat_1('#skF_5')) | ~m1_subset_1(D_36, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_30])).
% 2.35/1.34  tff(c_210, plain, (~m1_subset_1('#skF_2'(k2_relat_1('#skF_5'), k1_xboole_0), '#skF_4') | k2_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_206, c_96])).
% 2.35/1.34  tff(c_220, plain, (~m1_subset_1('#skF_2'(k2_relat_1('#skF_5'), k1_xboole_0), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_59, c_210])).
% 2.35/1.34  tff(c_205, plain, (![A_76]: (r2_hidden('#skF_2'(A_76, k1_xboole_0), A_76) | k1_xboole_0=A_76)), inference(resolution, [status(thm)], [c_10, c_201])).
% 2.35/1.34  tff(c_223, plain, (![A_78, B_79, C_80]: (m1_subset_1(k2_relset_1(A_78, B_79, C_80), k1_zfmisc_1(B_79)) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.35/1.34  tff(c_239, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_95, c_223])).
% 2.35/1.34  tff(c_245, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_239])).
% 2.35/1.34  tff(c_12, plain, (![A_5, C_7, B_6]: (m1_subset_1(A_5, C_7) | ~m1_subset_1(B_6, k1_zfmisc_1(C_7)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.35/1.34  tff(c_276, plain, (![A_83]: (m1_subset_1(A_83, '#skF_4') | ~r2_hidden(A_83, k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_245, c_12])).
% 2.35/1.34  tff(c_284, plain, (m1_subset_1('#skF_2'(k2_relat_1('#skF_5'), k1_xboole_0), '#skF_4') | k2_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_205, c_276])).
% 2.35/1.34  tff(c_310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_220, c_284])).
% 2.35/1.34  tff(c_311, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 2.35/1.34  tff(c_395, plain, (![A_101, B_102, C_103]: (k1_relset_1(A_101, B_102, C_103)=k1_relat_1(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.35/1.34  tff(c_398, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_395])).
% 2.35/1.34  tff(c_400, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_311, c_398])).
% 2.35/1.34  tff(c_402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_400])).
% 2.35/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.35  
% 2.35/1.35  Inference rules
% 2.35/1.35  ----------------------
% 2.35/1.35  #Ref     : 0
% 2.35/1.35  #Sup     : 72
% 2.35/1.35  #Fact    : 0
% 2.35/1.35  #Define  : 0
% 2.35/1.35  #Split   : 2
% 2.35/1.35  #Chain   : 0
% 2.35/1.35  #Close   : 0
% 2.35/1.35  
% 2.35/1.35  Ordering : KBO
% 2.35/1.35  
% 2.35/1.35  Simplification rules
% 2.35/1.35  ----------------------
% 2.35/1.35  #Subsume      : 3
% 2.35/1.35  #Demod        : 7
% 2.35/1.35  #Tautology    : 26
% 2.35/1.35  #SimpNegUnit  : 5
% 2.35/1.35  #BackRed      : 2
% 2.35/1.35  
% 2.35/1.35  #Partial instantiations: 0
% 2.35/1.35  #Strategies tried      : 1
% 2.35/1.35  
% 2.35/1.35  Timing (in seconds)
% 2.35/1.35  ----------------------
% 2.35/1.35  Preprocessing        : 0.34
% 2.35/1.35  Parsing              : 0.18
% 2.35/1.35  CNF conversion       : 0.03
% 2.35/1.35  Main loop            : 0.25
% 2.35/1.35  Inferencing          : 0.11
% 2.35/1.35  Reduction            : 0.06
% 2.35/1.35  Demodulation         : 0.04
% 2.35/1.35  BG Simplification    : 0.02
% 2.35/1.35  Subsumption          : 0.04
% 2.35/1.35  Abstraction          : 0.01
% 2.35/1.35  MUC search           : 0.00
% 2.35/1.35  Cooper               : 0.00
% 2.35/1.35  Total                : 0.62
% 2.35/1.35  Index Insertion      : 0.00
% 2.35/1.35  Index Deletion       : 0.00
% 2.35/1.35  Index Matching       : 0.00
% 2.35/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:27 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 147 expanded)
%              Number of leaves         :   35 (  64 expanded)
%              Depth                    :    9
%              Number of atoms          :  104 ( 283 expanded)
%              Number of equality atoms :   32 (  72 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
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

tff(f_65,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_42,plain,(
    k2_relset_1('#skF_5','#skF_4','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_26,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_79,plain,(
    ! [B_55,A_56] :
      ( v1_relat_1(B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_56))
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_89,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_79])).

tff(c_94,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_89])).

tff(c_96,plain,(
    ! [A_59] :
      ( k1_relat_1(A_59) = k1_xboole_0
      | k2_relat_1(A_59) != k1_xboole_0
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_103,plain,
    ( k1_relat_1('#skF_6') = k1_xboole_0
    | k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_94,c_96])).

tff(c_105,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_106,plain,(
    ! [A_60] :
      ( k2_relat_1(A_60) = k1_xboole_0
      | k1_relat_1(A_60) != k1_xboole_0
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_109,plain,
    ( k2_relat_1('#skF_6') = k1_xboole_0
    | k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_94,c_106])).

tff(c_115,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_109])).

tff(c_154,plain,(
    ! [C_70,A_71,B_72] :
      ( v4_relat_1(C_70,A_71)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_168,plain,(
    v4_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_154])).

tff(c_24,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_69,plain,(
    ! [C_51,A_52] :
      ( r2_hidden(C_51,k1_zfmisc_1(A_52))
      | ~ r1_tarski(C_51,A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_77,plain,(
    ! [C_51,A_52] :
      ( m1_subset_1(C_51,k1_zfmisc_1(A_52))
      | ~ r1_tarski(C_51,A_52) ) ),
    inference(resolution,[status(thm)],[c_69,c_16])).

tff(c_194,plain,(
    ! [A_79,C_80,B_81] :
      ( m1_subset_1(A_79,C_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(C_80))
      | ~ r2_hidden(A_79,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_254,plain,(
    ! [A_90,A_91,C_92] :
      ( m1_subset_1(A_90,A_91)
      | ~ r2_hidden(A_90,C_92)
      | ~ r1_tarski(C_92,A_91) ) ),
    inference(resolution,[status(thm)],[c_77,c_194])).

tff(c_261,plain,(
    ! [A_93,A_94] :
      ( m1_subset_1('#skF_1'(A_93),A_94)
      | ~ r1_tarski(A_93,A_94)
      | k1_xboole_0 = A_93 ) ),
    inference(resolution,[status(thm)],[c_2,c_254])).

tff(c_206,plain,(
    ! [A_83,B_84,C_85] :
      ( k1_relset_1(A_83,B_84,C_85) = k1_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_220,plain,(
    k1_relset_1('#skF_5','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_206])).

tff(c_63,plain,(
    ! [D_50] :
      ( ~ r2_hidden(D_50,k1_relset_1('#skF_5','#skF_4','#skF_6'))
      | ~ m1_subset_1(D_50,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_68,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_5','#skF_4','#skF_6')),'#skF_5')
    | k1_relset_1('#skF_5','#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_63])).

tff(c_117,plain,(
    ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_5','#skF_4','#skF_6')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_221,plain,(
    ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_6')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_117])).

tff(c_268,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_5')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_261,c_221])).

tff(c_291,plain,(
    ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_268])).

tff(c_299,plain,
    ( ~ v4_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_291])).

tff(c_303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_168,c_299])).

tff(c_304,plain,(
    k1_relset_1('#skF_5','#skF_4','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_500,plain,(
    ! [A_146,B_147,C_148] :
      ( k1_relset_1(A_146,B_147,C_148) = k1_relat_1(C_148)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_515,plain,(
    k1_relset_1('#skF_5','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_500])).

tff(c_520,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_515])).

tff(c_522,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_520])).

tff(c_524,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_725,plain,(
    ! [A_183,B_184,C_185] :
      ( k2_relset_1(A_183,B_184,C_185) = k2_relat_1(C_185)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_740,plain,(
    k2_relset_1('#skF_5','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_725])).

tff(c_745,plain,(
    k2_relset_1('#skF_5','#skF_4','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_740])).

tff(c_747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_745])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:21:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.48  
% 2.95/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.48  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 2.95/1.48  
% 2.95/1.48  %Foreground sorts:
% 2.95/1.48  
% 2.95/1.48  
% 2.95/1.48  %Background operators:
% 2.95/1.48  
% 2.95/1.48  
% 2.95/1.48  %Foreground operators:
% 2.95/1.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.95/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.95/1.48  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.95/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.95/1.48  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.95/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.95/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.95/1.48  tff('#skF_5', type, '#skF_5': $i).
% 2.95/1.48  tff('#skF_6', type, '#skF_6': $i).
% 2.95/1.48  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.95/1.48  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.95/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.95/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.95/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.95/1.48  tff('#skF_4', type, '#skF_4': $i).
% 2.95/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.95/1.48  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.95/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.95/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.95/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.95/1.48  
% 2.95/1.49  tff(f_106, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 2.95/1.49  tff(f_65, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.95/1.49  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.95/1.49  tff(f_71, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 2.95/1.49  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.95/1.49  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.95/1.49  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.95/1.49  tff(f_40, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.95/1.49  tff(f_44, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.95/1.49  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.95/1.49  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.95/1.49  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.95/1.49  tff(c_42, plain, (k2_relset_1('#skF_5', '#skF_4', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.95/1.49  tff(c_26, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.95/1.49  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.95/1.49  tff(c_79, plain, (![B_55, A_56]: (v1_relat_1(B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_56)) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.95/1.49  tff(c_89, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_79])).
% 2.95/1.49  tff(c_94, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_89])).
% 2.95/1.49  tff(c_96, plain, (![A_59]: (k1_relat_1(A_59)=k1_xboole_0 | k2_relat_1(A_59)!=k1_xboole_0 | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.95/1.49  tff(c_103, plain, (k1_relat_1('#skF_6')=k1_xboole_0 | k2_relat_1('#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_94, c_96])).
% 2.95/1.49  tff(c_105, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_103])).
% 2.95/1.49  tff(c_106, plain, (![A_60]: (k2_relat_1(A_60)=k1_xboole_0 | k1_relat_1(A_60)!=k1_xboole_0 | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.95/1.49  tff(c_109, plain, (k2_relat_1('#skF_6')=k1_xboole_0 | k1_relat_1('#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_94, c_106])).
% 2.95/1.49  tff(c_115, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_105, c_109])).
% 2.95/1.49  tff(c_154, plain, (![C_70, A_71, B_72]: (v4_relat_1(C_70, A_71) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.95/1.49  tff(c_168, plain, (v4_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_154])).
% 2.95/1.49  tff(c_24, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(B_17), A_16) | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.95/1.49  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.95/1.49  tff(c_69, plain, (![C_51, A_52]: (r2_hidden(C_51, k1_zfmisc_1(A_52)) | ~r1_tarski(C_51, A_52))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.95/1.49  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.95/1.49  tff(c_77, plain, (![C_51, A_52]: (m1_subset_1(C_51, k1_zfmisc_1(A_52)) | ~r1_tarski(C_51, A_52))), inference(resolution, [status(thm)], [c_69, c_16])).
% 2.95/1.49  tff(c_194, plain, (![A_79, C_80, B_81]: (m1_subset_1(A_79, C_80) | ~m1_subset_1(B_81, k1_zfmisc_1(C_80)) | ~r2_hidden(A_79, B_81))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.95/1.49  tff(c_254, plain, (![A_90, A_91, C_92]: (m1_subset_1(A_90, A_91) | ~r2_hidden(A_90, C_92) | ~r1_tarski(C_92, A_91))), inference(resolution, [status(thm)], [c_77, c_194])).
% 2.95/1.49  tff(c_261, plain, (![A_93, A_94]: (m1_subset_1('#skF_1'(A_93), A_94) | ~r1_tarski(A_93, A_94) | k1_xboole_0=A_93)), inference(resolution, [status(thm)], [c_2, c_254])).
% 2.95/1.49  tff(c_206, plain, (![A_83, B_84, C_85]: (k1_relset_1(A_83, B_84, C_85)=k1_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.95/1.49  tff(c_220, plain, (k1_relset_1('#skF_5', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_206])).
% 2.95/1.49  tff(c_63, plain, (![D_50]: (~r2_hidden(D_50, k1_relset_1('#skF_5', '#skF_4', '#skF_6')) | ~m1_subset_1(D_50, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.95/1.49  tff(c_68, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_5', '#skF_4', '#skF_6')), '#skF_5') | k1_relset_1('#skF_5', '#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_63])).
% 2.95/1.49  tff(c_117, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_5', '#skF_4', '#skF_6')), '#skF_5')), inference(splitLeft, [status(thm)], [c_68])).
% 2.95/1.49  tff(c_221, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_6')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_220, c_117])).
% 2.95/1.49  tff(c_268, plain, (~r1_tarski(k1_relat_1('#skF_6'), '#skF_5') | k1_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_261, c_221])).
% 2.95/1.49  tff(c_291, plain, (~r1_tarski(k1_relat_1('#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_115, c_268])).
% 2.95/1.49  tff(c_299, plain, (~v4_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_24, c_291])).
% 2.95/1.49  tff(c_303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_168, c_299])).
% 2.95/1.49  tff(c_304, plain, (k1_relset_1('#skF_5', '#skF_4', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_68])).
% 2.95/1.49  tff(c_500, plain, (![A_146, B_147, C_148]: (k1_relset_1(A_146, B_147, C_148)=k1_relat_1(C_148) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.95/1.49  tff(c_515, plain, (k1_relset_1('#skF_5', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_500])).
% 2.95/1.49  tff(c_520, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_304, c_515])).
% 2.95/1.49  tff(c_522, plain, $false, inference(negUnitSimplification, [status(thm)], [c_115, c_520])).
% 2.95/1.49  tff(c_524, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_103])).
% 2.95/1.49  tff(c_725, plain, (![A_183, B_184, C_185]: (k2_relset_1(A_183, B_184, C_185)=k2_relat_1(C_185) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.95/1.49  tff(c_740, plain, (k2_relset_1('#skF_5', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_725])).
% 2.95/1.49  tff(c_745, plain, (k2_relset_1('#skF_5', '#skF_4', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_524, c_740])).
% 2.95/1.49  tff(c_747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_745])).
% 2.95/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.49  
% 2.95/1.49  Inference rules
% 2.95/1.49  ----------------------
% 2.95/1.49  #Ref     : 0
% 2.95/1.49  #Sup     : 142
% 2.95/1.49  #Fact    : 0
% 2.95/1.49  #Define  : 0
% 2.95/1.49  #Split   : 5
% 2.95/1.49  #Chain   : 0
% 2.95/1.49  #Close   : 0
% 2.95/1.49  
% 2.95/1.49  Ordering : KBO
% 2.95/1.49  
% 2.95/1.49  Simplification rules
% 2.95/1.49  ----------------------
% 2.95/1.49  #Subsume      : 7
% 2.95/1.49  #Demod        : 20
% 2.95/1.49  #Tautology    : 25
% 2.95/1.49  #SimpNegUnit  : 5
% 2.95/1.49  #BackRed      : 7
% 2.95/1.49  
% 2.95/1.49  #Partial instantiations: 0
% 2.95/1.49  #Strategies tried      : 1
% 2.95/1.49  
% 2.95/1.49  Timing (in seconds)
% 2.95/1.49  ----------------------
% 2.95/1.50  Preprocessing        : 0.35
% 2.95/1.50  Parsing              : 0.18
% 2.95/1.50  CNF conversion       : 0.03
% 2.95/1.50  Main loop            : 0.31
% 2.95/1.50  Inferencing          : 0.12
% 2.95/1.50  Reduction            : 0.09
% 2.95/1.50  Demodulation         : 0.06
% 2.95/1.50  BG Simplification    : 0.02
% 2.95/1.50  Subsumption          : 0.05
% 2.95/1.50  Abstraction          : 0.02
% 2.95/1.50  MUC search           : 0.00
% 2.95/1.50  Cooper               : 0.00
% 2.95/1.50  Total                : 0.70
% 2.95/1.50  Index Insertion      : 0.00
% 2.95/1.50  Index Deletion       : 0.00
% 2.95/1.50  Index Matching       : 0.00
% 2.95/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 10:08:17 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 149 expanded)
%              Number of leaves         :   35 (  64 expanded)
%              Depth                    :    9
%              Number of atoms          :  104 ( 288 expanded)
%              Number of equality atoms :   31 (  71 expanded)
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
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_65,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_42,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_26,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_79,plain,(
    ! [B_55,A_56] :
      ( v1_relat_1(B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_56))
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_89,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
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

tff(c_123,plain,(
    ! [C_62,B_63,A_64] :
      ( v5_relat_1(C_62,B_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_64,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_137,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_123])).

tff(c_24,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v5_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_294,plain,(
    ! [A_100,B_101,C_102] :
      ( k2_relset_1(A_100,B_101,C_102) = k2_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_313,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_294])).

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

tff(c_226,plain,(
    ! [A_86,A_87,C_88] :
      ( m1_subset_1(A_86,A_87)
      | ~ r2_hidden(A_86,C_88)
      | ~ r1_tarski(C_88,A_87) ) ),
    inference(resolution,[status(thm)],[c_77,c_194])).

tff(c_233,plain,(
    ! [A_89,A_90] :
      ( m1_subset_1('#skF_1'(A_89),A_90)
      | ~ r1_tarski(A_89,A_90)
      | k1_xboole_0 = A_89 ) ),
    inference(resolution,[status(thm)],[c_2,c_226])).

tff(c_63,plain,(
    ! [D_50] :
      ( ~ r2_hidden(D_50,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1(D_50,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_68,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_4','#skF_5','#skF_6')),'#skF_5')
    | k2_relset_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_63])).

tff(c_117,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_260,plain,
    ( ~ r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),'#skF_5')
    | k2_relset_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_233,c_117])).

tff(c_262,plain,(
    ~ r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_260])).

tff(c_315,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_262])).

tff(c_332,plain,
    ( ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_315])).

tff(c_336,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_137,c_332])).

tff(c_337,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_356,plain,(
    ! [A_104,B_105,C_106] :
      ( k2_relset_1(A_104,B_105,C_106) = k2_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_371,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_356])).

tff(c_376,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_371])).

tff(c_378,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_376])).

tff(c_379,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_509,plain,(
    ! [A_135,B_136,C_137] :
      ( k2_relset_1(A_135,B_136,C_137) = k2_relat_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_524,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_509])).

tff(c_529,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_524])).

tff(c_531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_529])).

tff(c_532,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_674,plain,(
    ! [A_166,B_167,C_168] :
      ( k1_relset_1(A_166,B_167,C_168) = k1_relat_1(C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_685,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_674])).

tff(c_689,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_685])).

tff(c_691,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_689])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:28:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.80  
% 2.91/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.81  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 2.91/1.81  
% 2.91/1.81  %Foreground sorts:
% 2.91/1.81  
% 2.91/1.81  
% 2.91/1.81  %Background operators:
% 2.91/1.81  
% 2.91/1.81  
% 2.91/1.81  %Foreground operators:
% 2.91/1.81  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.91/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.91/1.81  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.91/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.91/1.81  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.91/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.91/1.81  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.91/1.81  tff('#skF_5', type, '#skF_5': $i).
% 2.91/1.81  tff('#skF_6', type, '#skF_6': $i).
% 2.91/1.81  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.91/1.81  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.91/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.91/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.91/1.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.91/1.81  tff('#skF_4', type, '#skF_4': $i).
% 2.91/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.81  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.91/1.81  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.91/1.81  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.91/1.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.91/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.91/1.81  
% 3.17/1.82  tff(f_106, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 3.17/1.82  tff(f_65, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.17/1.82  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.17/1.82  tff(f_71, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 3.17/1.82  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.17/1.82  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.17/1.82  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.17/1.82  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.17/1.82  tff(f_40, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.17/1.82  tff(f_44, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.17/1.82  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.17/1.82  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.17/1.82  tff(c_42, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.17/1.82  tff(c_26, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.17/1.82  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.17/1.82  tff(c_79, plain, (![B_55, A_56]: (v1_relat_1(B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_56)) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.17/1.82  tff(c_89, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_79])).
% 3.17/1.82  tff(c_94, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_89])).
% 3.17/1.82  tff(c_96, plain, (![A_59]: (k1_relat_1(A_59)=k1_xboole_0 | k2_relat_1(A_59)!=k1_xboole_0 | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.17/1.82  tff(c_103, plain, (k1_relat_1('#skF_6')=k1_xboole_0 | k2_relat_1('#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_94, c_96])).
% 3.17/1.82  tff(c_105, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_103])).
% 3.17/1.82  tff(c_123, plain, (![C_62, B_63, A_64]: (v5_relat_1(C_62, B_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_64, B_63))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.17/1.82  tff(c_137, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_123])).
% 3.17/1.82  tff(c_24, plain, (![B_17, A_16]: (r1_tarski(k2_relat_1(B_17), A_16) | ~v5_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.17/1.82  tff(c_294, plain, (![A_100, B_101, C_102]: (k2_relset_1(A_100, B_101, C_102)=k2_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.17/1.82  tff(c_313, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_294])).
% 3.17/1.82  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.17/1.82  tff(c_69, plain, (![C_51, A_52]: (r2_hidden(C_51, k1_zfmisc_1(A_52)) | ~r1_tarski(C_51, A_52))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.17/1.82  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.17/1.82  tff(c_77, plain, (![C_51, A_52]: (m1_subset_1(C_51, k1_zfmisc_1(A_52)) | ~r1_tarski(C_51, A_52))), inference(resolution, [status(thm)], [c_69, c_16])).
% 3.17/1.82  tff(c_194, plain, (![A_79, C_80, B_81]: (m1_subset_1(A_79, C_80) | ~m1_subset_1(B_81, k1_zfmisc_1(C_80)) | ~r2_hidden(A_79, B_81))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.17/1.82  tff(c_226, plain, (![A_86, A_87, C_88]: (m1_subset_1(A_86, A_87) | ~r2_hidden(A_86, C_88) | ~r1_tarski(C_88, A_87))), inference(resolution, [status(thm)], [c_77, c_194])).
% 3.17/1.82  tff(c_233, plain, (![A_89, A_90]: (m1_subset_1('#skF_1'(A_89), A_90) | ~r1_tarski(A_89, A_90) | k1_xboole_0=A_89)), inference(resolution, [status(thm)], [c_2, c_226])).
% 3.17/1.82  tff(c_63, plain, (![D_50]: (~r2_hidden(D_50, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1(D_50, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.17/1.82  tff(c_68, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_4', '#skF_5', '#skF_6')), '#skF_5') | k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_63])).
% 3.17/1.82  tff(c_117, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_4', '#skF_5', '#skF_6')), '#skF_5')), inference(splitLeft, [status(thm)], [c_68])).
% 3.17/1.82  tff(c_260, plain, (~r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), '#skF_5') | k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_233, c_117])).
% 3.17/1.82  tff(c_262, plain, (~r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_260])).
% 3.17/1.82  tff(c_315, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_313, c_262])).
% 3.17/1.82  tff(c_332, plain, (~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_24, c_315])).
% 3.17/1.82  tff(c_336, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_137, c_332])).
% 3.17/1.82  tff(c_337, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_260])).
% 3.17/1.82  tff(c_356, plain, (![A_104, B_105, C_106]: (k2_relset_1(A_104, B_105, C_106)=k2_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.17/1.82  tff(c_371, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_356])).
% 3.17/1.82  tff(c_376, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_337, c_371])).
% 3.17/1.82  tff(c_378, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_376])).
% 3.17/1.82  tff(c_379, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_68])).
% 3.17/1.82  tff(c_509, plain, (![A_135, B_136, C_137]: (k2_relset_1(A_135, B_136, C_137)=k2_relat_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.17/1.82  tff(c_524, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_509])).
% 3.17/1.82  tff(c_529, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_379, c_524])).
% 3.17/1.82  tff(c_531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_529])).
% 3.17/1.82  tff(c_532, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_103])).
% 3.17/1.82  tff(c_674, plain, (![A_166, B_167, C_168]: (k1_relset_1(A_166, B_167, C_168)=k1_relat_1(C_168) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.17/1.82  tff(c_685, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_674])).
% 3.17/1.82  tff(c_689, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_532, c_685])).
% 3.17/1.82  tff(c_691, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_689])).
% 3.17/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.82  
% 3.17/1.82  Inference rules
% 3.17/1.82  ----------------------
% 3.17/1.82  #Ref     : 0
% 3.17/1.82  #Sup     : 130
% 3.17/1.82  #Fact    : 0
% 3.17/1.82  #Define  : 0
% 3.17/1.82  #Split   : 7
% 3.17/1.82  #Chain   : 0
% 3.17/1.82  #Close   : 0
% 3.17/1.82  
% 3.17/1.82  Ordering : KBO
% 3.17/1.82  
% 3.17/1.82  Simplification rules
% 3.17/1.82  ----------------------
% 3.17/1.82  #Subsume      : 3
% 3.17/1.82  #Demod        : 22
% 3.17/1.82  #Tautology    : 23
% 3.17/1.82  #SimpNegUnit  : 5
% 3.17/1.82  #BackRed      : 7
% 3.17/1.82  
% 3.17/1.82  #Partial instantiations: 0
% 3.17/1.82  #Strategies tried      : 1
% 3.17/1.82  
% 3.17/1.82  Timing (in seconds)
% 3.17/1.82  ----------------------
% 3.17/1.82  Preprocessing        : 0.48
% 3.17/1.82  Parsing              : 0.26
% 3.17/1.82  CNF conversion       : 0.04
% 3.17/1.82  Main loop            : 0.40
% 3.17/1.83  Inferencing          : 0.15
% 3.17/1.83  Reduction            : 0.11
% 3.17/1.83  Demodulation         : 0.08
% 3.17/1.83  BG Simplification    : 0.02
% 3.17/1.83  Subsumption          : 0.06
% 3.17/1.83  Abstraction          : 0.02
% 3.17/1.83  MUC search           : 0.00
% 3.17/1.83  Cooper               : 0.00
% 3.17/1.83  Total                : 0.92
% 3.17/1.83  Index Insertion      : 0.00
% 3.17/1.83  Index Deletion       : 0.00
% 3.17/1.83  Index Matching       : 0.00
% 3.17/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
